"""Fresh read-only exact-VM describe, retaining complete native authentication evidence."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import uuid
from finalize_builder02_bootstrap import SDK, FLAGS, VM, ID

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    folder = HERE / ('full109-auth-vm-recheck-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + uuid.uuid4().hex[:8])
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    source = Path(__file__).read_bytes()
    (folder / 'control.snapshot.py').write_bytes(source)
    argv = [SDK, 'compute', 'instances', 'describe', VM,
            '--format=json(name,id,status,zone,machineType,networkInterfaces)', *FLAGS]
    record = dict(argv=argv, started_utc=datetime.now(timezone.utc).isoformat(),
                  source_sha256=sha(source), read_only=True, no_vm_power_or_ssh=True)
    with (folder / 'stdout').open('xb') as out, (folder / 'stderr').open('xb') as err:
        process = subprocess.Popen(argv, stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
        record['pid'] = process.pid
        (folder / 'command.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
        while True:
            try:
                native = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                print(json.dumps(dict(folder=str(folder), original_pid=process.pid, still_running=True)), flush=True)
    output, error = [(folder / name).read_bytes() for name in ('stdout', 'stderr')]
    record.update(native_exit=native, finished_utc=datetime.now(timezone.utc).isoformat(),
                  stdout_sha256=sha(output), stderr_sha256=sha(error))
    (folder / 'command.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    state = None
    if native == 0:
        state = json.loads(output)
        assert state['name'] == VM and str(state['id']) == ID
        assert state['zone'].rsplit('/', 1)[-1] == 'us-central1-a'
        assert state['machineType'].rsplit('/', 1)[-1] == 'e2-highmem-8'
        assert not any(nic.get('accessConfigs') for nic in state['networkInterfaces'])
    result = dict(native_exit=native, exact_authenticated_state=state,
                  reauthentication_required=b'Reauthentication failed' in error,
                  read_only=True, compiler_invoked=False, vm_power_operation=False,
                  launch_clearance=False, accepted=False)
    (folder / 'result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(folder), **result)), flush=True)
    raise SystemExit(native)


if __name__ == '__main__':
    main()
