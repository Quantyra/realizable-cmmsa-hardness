"""Preserve read-only VM state and serial diagnostics after terminal IAP failures."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
from custody_checks import digest
from finalize_builder02_bootstrap import SDK, FLAGS, VM, ID

HERE = Path(__file__).resolve().parent


def main():
    folder = HERE / ('full109-ssh-transport-inspection-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (folder / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    records = []

    def call(args):
        number = len(records)
        argv = [SDK, *args, *FLAGS]
        with (folder / f'{number}.stdout').open('xb') as out, (folder / f'{number}.stderr').open('xb') as err:
            child = subprocess.Popen(argv, stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
            while True:
                try:
                    native = child.wait(timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    print(json.dumps(dict(original_pid=child.pid, still_running=True)), flush=True)
        row = dict(argv=argv, native_exit=native, finished_utc=datetime.now(timezone.utc).isoformat(),
                   stdout_sha256=digest(folder / f'{number}.stdout'), stderr_sha256=digest(folder / f'{number}.stderr'))
        records.append(row)
        (folder / 'commands.json').write_text(json.dumps(records, indent=2)+'\n', encoding='utf-8')
        assert native == 0, 'Preserve failed read-only diagnostic'
        return (folder / f'{number}.stdout').read_bytes()

    state = json.loads(call(['compute', 'instances', 'describe', VM,
        '--format=json(name,id,status,zone,machineType,networkInterfaces,lastStartTimestamp,lastStopTimestamp)']))
    assert state['name'] == VM and str(state['id']) == ID
    assert state['zone'].endswith('/us-central1-a') and state['machineType'].endswith('/e2-highmem-8')
    assert not any(nic.get('accessConfigs') for nic in state['networkInterfaces'])
    call(['compute', 'instances', 'get-serial-port-output', VM, '--port=1', '--start=0'])
    result = dict(state=state, commands=records, read_only=True, compiler_invoked=False, vm_power_operation=False)
    (folder / 'result.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(folder), state=state, native_exits=[r['native_exit'] for r in records])), flush=True)


if __name__ == '__main__':
    main()
