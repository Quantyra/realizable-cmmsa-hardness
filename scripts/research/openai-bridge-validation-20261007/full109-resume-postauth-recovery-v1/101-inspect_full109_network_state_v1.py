"""Read exact-VM effective firewalls and recent lifecycle logs without changing access."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
from custody_checks import digest
from finalize_builder02_bootstrap import SDK, FLAGS, VM, ID

HERE = Path(__file__).resolve().parent


def main():
    folder = HERE / ('full109-network-inspection-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (folder / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    records = []
    commands = [
        ['compute', 'instances', 'describe', VM, '--format=json(name,id,status,zone,machineType,networkInterfaces,tags,displayDevice,lastStartTimestamp,lastStopTimestamp)', *FLAGS],
        ['compute', 'instances', 'network-interfaces', 'get-effective-firewalls', VM, '--network-interface=nic0', '--format=json', *FLAGS],
        ['compute', 'instances', 'get-guest-attributes', VM, '--query-path=hostkeys/', '--format=json', *FLAGS],
        ['logging', 'read', 'resource.type="gce_instance" AND resource.labels.instance_id="'+ID+'" AND timestamp>="2026-10-11T00:00:00Z"', '--limit=100', '--format=json', *[f for f in FLAGS if not f.startswith('--zone=')]],
    ]
    for number, args in enumerate(commands):
        argv = [SDK, *args]
        with (folder / f'{number}.stdout').open('xb') as out, (folder / f'{number}.stderr').open('xb') as err:
            child = subprocess.Popen(argv, stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
            while True:
                try:
                    native = child.wait(timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    print(json.dumps(dict(original_pid=child.pid, still_running=True)), flush=True)
        records.append(dict(argv=argv, native_exit=native, finished_utc=datetime.now(timezone.utc).isoformat(),
            stdout_sha256=digest(folder / f'{number}.stdout'), stderr_sha256=digest(folder / f'{number}.stderr')))
        (folder / 'commands.json').write_text(json.dumps(records, indent=2)+'\n', encoding='utf-8')
        if number == 0:
            assert native == 0
            state = json.loads((folder / '0.stdout').read_bytes())
            assert state['name'] == VM and str(state['id']) == ID
            assert state['zone'].endswith('/us-central1-a') and state['machineType'].endswith('/e2-highmem-8')
            assert not any(nic.get('accessConfigs') for nic in state['networkInterfaces'])
    result = dict(state=state, native_exits=[r['native_exit'] for r in records], read_only=True,
                  firewall_or_metadata_changed=False, compiler_invoked=False, vm_power_operation=False)
    (folder / 'result.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(folder), **result)), flush=True)


if __name__ == '__main__':
    main()
