"""Refresh dedicated trace staging idle activity without starting or launching."""
from datetime import datetime, timezone
import json
from full109_builder02_controller import ROOT, VM, VM_ID, context, local_gates
from full109_capture_gates import validate_successor


def main():
    validate_successor()
    loaded, runner = context()
    local_gates(loaded['common'], loaded)
    if (ROOT/'launch-once.json').exists():
        raise RuntimeError('Compile already launched; retain original handle')
    folder = ROOT/'idle-refresh-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True)
    runner.VM = VM
    class IdleControl(runner.Control):
        def cloud(self, args, **kwargs):
            if args[:3] == ['compute', 'instances', 'describe'] and args[3] == VM:
                pass
            elif args[:2] == ['compute', 'ssh'] and args[2] == VM:
                pass
            else:
                raise RuntimeError('Only dedicated describe/SSH permitted')
            return super().cloud(args, **kwargs)
    control = IdleControl(folder)
    _, out, _ = control.cloud(['compute', 'instances', 'describe', VM,
        '--format=json(name,id,status,zone,machineType,networkInterfaces)'])
    state = json.loads(out)
    assert state['name'] == VM and str(state['id']) == VM_ID and state['status'] == 'RUNNING'
    assert state['zone'].rsplit('/',1)[-1] == 'us-central1-a'
    assert state['machineType'].rsplit('/',1)[-1] == 'e2-highmem-8'
    assert not any(nic.get('accessConfigs') for nic in state['networkInterfaces'])
    control.authenticated = True
    _, out, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
        '--command=set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer'])
    assert out.decode().splitlines()[-1] == 'active'
    local_gates(loaded['common'], loaded)
    result = dict(state=state, resource=ROOT.name, idle_timer_active=True,
        idle_activity_refreshed=True, power_operation=False, compiler_invoked=False,
        staged_inputs_modified=False, launch_clearance=False, accepted=False)
    with (folder/'idle-refreshed.json').open('x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2)
    print(json.dumps(dict(receipt=str(folder/'idle-refreshed.json'), refreshed=True)))


if __name__ == '__main__':
    main()
