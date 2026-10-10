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
    assert not (ROOT/'launch-once.json').exists() and SSH.is_file() and KEY.is_file()
    folder = ROOT/'scope3-remaining-only-controls-v1'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
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
            remote = '"""GCP-only continuation of independently verified interrupted scope3, no replay."""\nimport hashlib\nimport importlib.util\nimport json\nimport os\nfrom pathlib import Path\nimport shutil\nimport stat\n\nHOME=Path(\'/home/dfredriksen_quantyra_org\')\nCONTROL=HOME/\'full109-storage-cache-repoint-v3\'\nSOURCE_SHA=\'4D0FD1669D999F7583369CBAC94411F8449CE2C15CA12C39E63306B7A54184AC\'\nPLAN_SHA=\'9B2779606C54C2531688B7CC209E32F7C7AAFA75CFB8C88F5ACACF1CD3AEF581\'\nPARTIAL_SHA=\'B2B8FEFC2A7CBF7A004B3590AB2821505995314D87DA36F52789E9B2F9169B3C\'\nCOMPLETED=18781\ndef digest(path):\n    with path.open(\'rb\') as stream:return hashlib.file_digest(stream,\'sha256\').hexdigest().upper()\ndef validate_rows(plan,old,canonical):\n    assert len(plan[\'rows\'])==19233\n    for index,row in enumerate(plan[\'rows\']):\n        rel=Path(row[\'relative\']);assert not rel.is_absolute() and \'..\' not in rel.parts\n        path=old/rel;dest=canonical/rel;backup=path.with_name(path.name+\'.full95-repoint-backup\')\n        assert dest.resolve(strict=True).is_relative_to(canonical)\n        assert dest.stat().st_size==row[\'bytes\'] and digest(dest)==row[\'sha256\']\n        assert not backup.exists() and not backup.is_symlink()\n        if index<COMPLETED:\n            assert path.is_symlink() and path.readlink()==dest\n            assert path.resolve(strict=True)==dest.resolve(strict=True)\n        else:\n            assert not path.is_symlink() and path.resolve(strict=True).is_relative_to(old)\n            info=path.stat()\n            assert stat.S_ISREG(info.st_mode) and info.st_nlink==1\n            assert info.st_size==row[\'bytes\'] and digest(path)==row[\'sha256\']\ndef write_new(path,value):\n    with path.open(\'x\') as stream:json.dump(value,stream,indent=2);stream.write(\'\\n\')\ndef main():\n    source=CONTROL/\'full109_storage_cache_repoint_v3.py\'\n    assert digest(source)==SOURCE_SHA\n    spec=importlib.util.spec_from_file_location(\'original_scope3\',source)\n    original=importlib.util.module_from_spec(spec);spec.loader.exec_module(original)\n    old,canonical=original.guards()\n    for entry in Path(\'/proc\').iterdir():\n        if not entry.name.isdigit() or int(entry.name)==os.getpid():continue\n        try:args=(entry/\'cmdline\').read_bytes().split(b\'\\0\')\n        except (FileNotFoundError,PermissionError):continue\n        assert not (any(arg.endswith(b\'/full109_storage_cache_repoint_v3.py\') for arg in args) and b\'--execute\' in args)\n    assert digest(CONTROL/\'plan.json\')==PLAN_SHA\n    assert digest(CONTROL/\'partial-execution.json\')==PARTIAL_SHA\n    assert not (CONTROL/\'receipt.json\').exists()\n    once=json.loads((CONTROL/\'execute-once.json\').read_bytes())\n    assert once==dict(plan_sha256=PLAN_SHA,compiler_invoked=False)\n    plan=json.loads((CONTROL/\'plan.json\').read_bytes())\n    partial=json.loads((CONTROL/\'partial-execution.json\').read_bytes())\n    assert plan[\'old_root\']==str(old) and plan[\'canonical_root\']==str(canonical)\n    assert partial[\'applied\']==plan[\'rows\'][:18780]\n    for key in (\'warm_files_written\',\'source_or_project_object_files_changed\',\'failed_evidence_archive_changed\',\'compiler_invoked\'):\n        assert partial[key] is False\n    validate_rows(plan,old,canonical)\n    folder=CONTROL/\'remaining-only-v1\';folder.mkdir(exist_ok=False)\n    write_new(folder/\'continue-once.json\',dict(plan_sha256=PLAN_SHA,partial_sha256=PARTIAL_SHA,\n        independently_verified_completed_rows=COMPLETED,remaining_rows=452,original_execute_replayed=False))\n    applied=[]\n    for row in plan[\'rows\'][COMPLETED:]:\n        path=old/row[\'relative\'];dest=canonical/row[\'relative\']\n        assert not path.is_symlink() and digest(path)==row[\'sha256\'] and digest(dest)==row[\'sha256\']\n        backup=path.with_name(path.name+\'.full95-repoint-backup\')\n        assert not backup.exists() and not backup.is_symlink()\n        path.rename(backup)\n        try:\n            path.symlink_to(dest)\n            assert digest(path)==row[\'sha256\'] and digest(dest)==row[\'sha256\']\n        except BaseException:\n            if path.is_symlink():path.unlink()\n            backup.rename(path)\n            raise\n        backup.unlink();applied.append(row)\n        temporary=folder/\'progress.next.json\'\n        temporary.write_text(json.dumps(dict(applied_remaining=applied),indent=2)+\'\\n\')\n        temporary.replace(folder/\'progress.json\')\n    assert len(applied)==452 and digest(CONTROL/\'partial-execution.json\')==PARTIAL_SHA\n    assert digest(HOME/(original.RUN+\'_evidence.tar.gz\'))==original.ARCHIVE_SHA\n    for row in plan[\'rows\']:\n        path=old/row[\'relative\'];dest=canonical/row[\'relative\']\n        assert path.is_symlink() and path.readlink()==dest and digest(path)==row[\'sha256\']\n    receipt=dict(partial)\n    receipt.update(applied=plan[\'rows\'],disk_after_bytes=shutil.disk_usage(HOME).free,\n        content_identity_verified_after_repoint=True,reversible_by_copying_identical_canonical_bytes=True,\n        interrupted_original_preserved=True,original_partial_sha256=PARTIAL_SHA,\n        original_plan_sha256=PLAN_SHA,independently_verified_preexisting_rows=COMPLETED,\n        remaining_rows_applied=len(applied),original_execute_replayed=False)\n    assert receipt[\'disk_after_bytes\']>receipt[\'disk_before_bytes\']\n    write_new(folder/\'receipt.json\',receipt)\n    print(json.dumps(dict(receipt_sha256=digest(folder/\'receipt.json\'),receipt=receipt,\n        remaining_rows_applied=len(applied),original_execute_replayed=False,compiler_invoked=False)))\n\nif __name__==\'__main__\':main()\n'
            command = 'python3 -B -c '+shlex.quote(remote)
            options = ['-o', 'BatchMode=yes', '-o', 'IdentitiesOnly=yes', '-o', 'StrictHostKeyChecking=yes',
                       '-o', 'HostKeyAlgorithms=ssh-ed25519', '-o', 'GlobalKnownHostsFile=NUL',
                       '-o', 'UserKnownHostsFile='+str(known), '-o', 'HostKeyAlias=compute.'+VM_ID,
                       '-o', 'PasswordAuthentication=no', '-o', 'KbdInteractiveAuthentication=no',
                       '-o', 'ConnectTimeout=30', '-i', str(KEY), '-p', str(port), '-T']
            raw = call([str(SSH), *options, 'dfredriksen_quantyra_org@127.0.0.1', command])
            result = json.loads(raw)
            (folder/'inspection.json').write_text(json.dumps(result, indent=2)+'\n')
            print(json.dumps(dict(folder=str(folder), inspection={k:v for k,v in result.items() if k != "receipt"}, host_key_fingerprint=fingerprint)), flush=True)
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
