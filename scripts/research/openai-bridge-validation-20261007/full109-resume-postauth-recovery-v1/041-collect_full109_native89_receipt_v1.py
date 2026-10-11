"""Read existing scope3 state via IAP/OpenSSH and the already trusted host key."""
import base64
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shlex
import socket
import struct
import subprocess
import time
import winreg
from full109_builder02_controller import ROOT, VM, VM_ID, context, local_gates
from full109_capture_gates import validate_successor
from finalize_builder02_bootstrap import SDK, FLAGS

SSH = Path('C:/Windows/System32/OpenSSH/ssh.exe')
KEY = Path('C:/Users/dfred/.ssh/google_compute_engine')


def cached_host_line():
    alias = 'compute.'+VM_ID
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r'Software\SimonTatham\PuTTY\SshHostKeys') as key:
        value, kind = winreg.QueryValueEx(key, 'ssh-ed25519@22:'+alias)
    assert kind == winreg.REG_SZ
    x, y = [int(part, 16) for part in value.split(',')]
    p = 2**255-19
    d = -121665*pow(121666, -1, p) % p
    assert 0 <= x < p and 0 <= y < p
    assert (-x*x+y*y-1-d*x*x*y*y) % p == 0
    encoded = (y | ((x & 1) << 255)).to_bytes(32, 'little')
    decoded_y = int.from_bytes(encoded, 'little') & ((1 << 255)-1)
    parity = encoded[-1] >> 7
    xx = (decoded_y*decoded_y-1)*pow(d*decoded_y*decoded_y+1, -1, p) % p
    decoded_x = pow(xx, (p+3)//8, p)
    if decoded_x*decoded_x % p != xx:
        decoded_x = decoded_x*pow(2, (p-1)//4, p) % p
    assert decoded_x*decoded_x % p == xx
    if decoded_x & 1 != parity:
        decoded_x = p-decoded_x
    assert (decoded_x, decoded_y) == (x, y), 'Host-key conversion roundtrip failed'
    wire = struct.pack('>I', 11)+b'ssh-ed25519'+struct.pack('>I', 32)+encoded
    fingerprint = 'SHA256:'+base64.b64encode(hashlib.sha256(wire).digest()).decode().rstrip('=')
    return alias+' ssh-ed25519 '+base64.b64encode(wire).decode()+'\n', fingerprint


def main():
    validate_successor()
    loaded, _ = context()
    local_gates(loaded['common'], loaded)
    assert SSH.is_file() and KEY.is_file()
    failed = Path('C:\\Users\\dfred\\.quantyra\\builder02\\full109-exact-crosslevel-warning-repair-resource02\\consumption-v3\\cache-repoint-controls\\20261011T001909531238Z')
    wrapper = Path('C:\\Users\\dfred\\.quantyra\\builder02\\full109-exact-crosslevel-warning-repair-resource02\\research-resume-20261010\\20261011T001754489124Z')
    assert json.loads((wrapper/'command.json').read_bytes())['native_exit'] == 1
    assert hashlib.sha256((failed/'commands.json').read_bytes()).hexdigest().upper() == 'DBA5835E67C2CC2D835794435475D99292E079142D6694101E3876E2711D3613'
    assert hashlib.sha256((wrapper/'command.json').read_bytes()).hexdigest().upper() == '18473A873131FE4778BF2F859EFF7359386981142AEC85AA64345E6409744C61'
    assert not (ROOT/'consumption-v3/launch-once.json').exists()
    assert json.loads((ROOT/'launch-once.json').read_bytes())['run']=='cmmsa_a8_output_20261010T110328Z_0d5c26f4'
    folder = ROOT/'readonly-receipt-native89-v1'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True)
    records = []
    def call(args):
        process = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try:
                out, err = process.communicate(timeout=30)
                break
            except subprocess.TimeoutExpired:
                print('Original read-only transport remains live', process.pid, flush=True)
        i = len(records)
        (folder/f'{i}.stdout').write_bytes(out); (folder/f'{i}.stderr').write_bytes(err)
        records.append(dict(argv=args, native_exit=process.returncode,
                            stdout_sha256=hashlib.sha256(out).hexdigest().upper(),
                            stderr_sha256=hashlib.sha256(err).hexdigest().upper()))
        (folder/'commands.json').write_text(json.dumps(records, indent=2)+'\n')
        assert process.returncode == 0, 'Read-only transport failed; preserve original receipts'
        return out
    state = json.loads(call([SDK, 'compute', 'instances', 'describe', VM,
                             '--format=json(name,id,status,zone,machineType,networkInterfaces)', *FLAGS]))
    assert state['name'] == VM and str(state['id']) == VM_ID and state['status'] == 'RUNNING'
    assert state['zone'].rsplit('/', 1)[-1] == 'us-central1-a'
    assert state['machineType'].rsplit('/', 1)[-1] == 'e2-highmem-8'
    assert not any(nic.get('accessConfigs') for nic in state['networkInterfaces'])
    line, fingerprint = cached_host_line()
    known = folder/'known_hosts'; known.write_text(line, encoding='ascii')
    with socket.socket() as reservation:
        reservation.bind(('127.0.0.1', 0)); port = reservation.getsockname()[1]
    args = [SDK, 'compute', 'start-iap-tunnel', VM, '22',
            '--local-host-port=127.0.0.1:'+str(port), *FLAGS]
    with (folder/'tunnel.stdout').open('xb') as out, (folder/'tunnel.stderr').open('xb') as err:
        tunnel = subprocess.Popen(args, stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
        (folder/'tunnel-start.json').write_text(json.dumps(dict(argv=args, pid=tunnel.pid,
            host_key_source='Existing PuTTY cached compute.'+VM_ID, host_key_fingerprint=fingerprint,
            conversion_roundtrip_verified=True, private_key_contents_logged=False,
            original_SDK_sessions_modified=False), indent=2)+'\n')
        try:
            deadline = time.monotonic()+60
            while True:
                assert tunnel.poll() is None, 'Owned IAP tunnel exited before connection'
                try:
                    with socket.create_connection(('127.0.0.1', port), timeout=1):
                        break
                except OSError:
                    assert time.monotonic() < deadline, 'Owned tunnel readiness unresolved'
                    time.sleep(0.2)
            remote = "import base64,hashlib,json,os,urllib.request\nfrom pathlib import Path\no=urllib.request.build_opener(urllib.request.ProxyHandler({}))\nr=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})\nwith o.open(r,timeout=10) as response:\n assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'\nhome=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home\nroot=Path('/home/dfredriksen_quantyra_org/full109-trace-cache-small-native89-v1')\nassert (root/'execute-once.json').is_file()\nassert hashlib.sha256((root/'full109_trace_cache_small_native89_v1.py').read_bytes()).hexdigest().upper()=='0C90D92321DFBAE6587BA3C8A1C4FCC79005BAFA2CD8BFCD10F40D2FEF22FDFA'\nfor entry in Path('/proc').iterdir():\n if not entry.name.isdigit() or int(entry.name)==os.getpid():continue\n try:name=(entry/'comm').read_text().strip();args=(entry/'cmdline').read_bytes()\n except (FileNotFoundError,PermissionError):continue\n assert not (name=='python3' and b'full109_trace_cache_small_native89_v1.py' in args), 'Original recovery still live'\ndata=(root/'receipt.json').read_bytes()\nassert hashlib.sha256(data).hexdigest().upper()=='17BDA840557AB015CD086F91E18D68CFB078343779521C57BF2A273F90EA64BA'\nvalue=json.loads(data);assert len(value['applied'])==19233\nprint(json.dumps(dict(receipt_sha256='17BDA840557AB015CD086F91E18D68CFB078343779521C57BF2A273F90EA64BA',raw_receipt_base64=base64.b64encode(data).decode(),read_only=True,execution_replayed=False,compiler_invoked=False)))\n"
            command = 'python3 -B -c '+shlex.quote(remote)
            options = ['-o', 'BatchMode=yes', '-o', 'IdentitiesOnly=yes', '-o', 'StrictHostKeyChecking=yes',
                       '-o', 'HostKeyAlgorithms=ssh-ed25519', '-o', 'GlobalKnownHostsFile=NUL',
                       '-o', 'UserKnownHostsFile='+str(known), '-o', 'HostKeyAlias=compute.'+VM_ID,
                       '-o', 'PasswordAuthentication=no', '-o', 'KbdInteractiveAuthentication=no',
                       '-o', 'ConnectTimeout=30', '-i', str(KEY), '-p', str(port), '-T']
            raw = call([str(SSH), *options, 'dfredriksen_quantyra_org@127.0.0.1', command])
            result = json.loads(raw)
            (folder/'inspection.json').write_text(json.dumps(result, indent=2)+'\n')
            print(json.dumps(dict(folder=str(folder), inspection={k:v for k,v in result.items() if k != "raw_receipt_base64"}, host_key_fingerprint=fingerprint)), flush=True)
        finally:
            if tunnel.poll() is None:
                cleanup = subprocess.run(['taskkill.exe', '/PID', str(tunnel.pid), '/T', '/F'],
                                         capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
                (folder/'owned-tunnel-cleanup.stdout').write_bytes(cleanup.stdout)
                (folder/'owned-tunnel-cleanup.stderr').write_bytes(cleanup.stderr)
                (folder/'owned-tunnel-cleanup.json').write_text(json.dumps(dict(pid=tunnel.pid,
                    native_exit=cleanup.returncode, only_owned_tunnel_targeted=True))+'\n')
            tunnel.wait()


if __name__ == '__main__':
    main()
