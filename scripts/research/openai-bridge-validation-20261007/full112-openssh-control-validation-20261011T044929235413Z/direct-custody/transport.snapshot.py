"""Exact dedicated02 IAP/OpenSSH transport; preserve complete native command bytes."""
from datetime import datetime, timezone
import json
from pathlib import Path
import socket
import subprocess
import time
from custody_checks import digest
from inspect_full111_native_progress_v1 import cached_host_line, SSH, KEY
from full111_builder02_controller import VM, VM_ID
from finalize_builder02_bootstrap import SDK, FLAGS


class Session:
    def __init__(self, folder):
        self.folder = Path(folder)
        self.folder.mkdir(exist_ok=False)
        self.records = []
        self.tunnel = None
        self.streams = []
        (self.folder/'transport.snapshot.py').write_bytes(Path(__file__).read_bytes())

    def call(self, argv, data=None, allow_failure=False, output_path=None):
        number = len(self.records)
        prefix = self.folder / f'{number:03d}'
        row = dict(argv=argv, started_utc=datetime.now(timezone.utc).isoformat())
        if data is not None:
            prefix.with_suffix('.stdin').open('xb').write(data)
            row['stdin_sha256'] = digest(prefix.with_suffix('.stdin'))
        stdout_path = Path(output_path) if output_path is not None else prefix.with_suffix('.stdout')
        with stdout_path.open('xb') as out, prefix.with_suffix('.stderr').open('xb') as err:
            process = subprocess.Popen(argv, stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,
                stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
            row['pid'] = process.pid
            (self.folder/'active-command.json').write_text(json.dumps(row, indent=2)+'\n')
            first = True
            while True:
                try:
                    process.communicate(input=data if first else None, timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    first = False
                    print(json.dumps(dict(original_transport_live=process.pid, command=number)), flush=True)
        row.update(native_exit=process.returncode, finished_utc=datetime.now(timezone.utc).isoformat())
        for stream in ('stdout', 'stderr'):
            path = stdout_path if stream == 'stdout' else prefix.with_suffix('.stderr')
            row[stream+'_path'] = str(path)
            row[stream+'_sha256'] = digest(path)
        self.records.append(row)
        (self.folder/'commands.json').write_text(json.dumps(self.records, indent=2)+'\n')
        assert process.returncode == 0 or allow_failure, 'Original transport failed; preserve and collect without replay'
        return stdout_path

    def __enter__(self):
        assert SSH.is_file() and KEY.is_file()
        path = self.call([SDK, 'compute', 'instances', 'describe', VM,
            '--format=json(name,id,status,zone,machineType,networkInterfaces)', *FLAGS])
        self.state = json.loads(path.read_bytes())
        state = self.state
        assert state['name'] == VM and str(state['id']) == VM_ID and state['status'] == 'RUNNING'
        assert state['zone'].rsplit('/', 1)[-1] == 'us-central1-a'
        assert state['machineType'].rsplit('/', 1)[-1] == 'e2-highmem-8'
        assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
        line, fingerprint = cached_host_line()
        known = self.folder/'known_hosts'; known.write_text(line, encoding='ascii')
        with socket.socket() as reservation:
            reservation.bind(('127.0.0.1', 0)); port = reservation.getsockname()[1]
        argv = [SDK, 'compute', 'start-iap-tunnel', VM, '22', '--local-host-port=127.0.0.1:'+str(port), *FLAGS]
        self.streams = [(self.folder/('tunnel.'+s)).open('xb') for s in ('stdout','stderr')]
        self.tunnel = subprocess.Popen(argv, stdout=self.streams[0], stderr=self.streams[1], creationflags=subprocess.CREATE_NO_WINDOW)
        (self.folder/'tunnel-start.json').write_text(json.dumps(dict(argv=argv,pid=self.tunnel.pid,
            host_key_fingerprint=fingerprint,existing_cached_key_roundtrip_verified=True,
            private_key_contents_logged=False),indent=2)+'\n')
        try:
            deadline = time.monotonic()+60
            while True:
                assert self.tunnel.poll() is None, 'Owned tunnel terminated before readiness'
                try:
                    with socket.create_connection(('127.0.0.1', port), timeout=1): break
                except OSError:
                    assert time.monotonic() < deadline, 'Owned tunnel readiness unresolved'
                    time.sleep(0.2)
            self.ssh_argv = [str(SSH), '-o','BatchMode=yes','-o','IdentitiesOnly=yes',
                '-o','StrictHostKeyChecking=yes','-o','HostKeyAlgorithms=ssh-ed25519',
                '-o','GlobalKnownHostsFile=NUL','-o','UserKnownHostsFile='+str(known),
                '-o','HostKeyAlias=compute.'+VM_ID,'-o','PasswordAuthentication=no',
                '-o','KbdInteractiveAuthentication=no','-o','ConnectTimeout=30',
                '-i',str(KEY),'-p',str(port),'-T','dfredriksen_quantyra_org@127.0.0.1']
            return self
        except BaseException:
            self.close()
            raise

    def ssh(self, command, allow_failure=False, output_path=None):
        return self.call([*self.ssh_argv, command], allow_failure=allow_failure, output_path=output_path)

    def python(self, code):
        return self.call([*self.ssh_argv, 'python3 -B -'], code.encode('utf-8'))

    def close(self):
        if self.tunnel is not None:
            if self.tunnel.poll() is None:
                self.call(['taskkill.exe','/PID',str(self.tunnel.pid),'/T','/F'])
            self.tunnel.wait()
        for stream in self.streams: stream.close()

    def __exit__(self, kind, value, trace):
        self.close()

