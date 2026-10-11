"""Resume settled trace preparation after a newly verified VM termination."""
import json
from full109_builder02_controller import ROOT, VM, VM_ID, context, local_gates
from full109_consumption_v3_controller import ready


def main():
    ready()
    loaded, runner = context()
    local_gates(loaded['common'], loaded)
    trace = ROOT/'consumption-v3'
    assert not (trace/'launch-once.json').exists()
    previous = json.loads((trace/'settled-cache-recovery-boot-v2/boot-result.json').read_bytes())
    assert previous['after']['status'] == 'RUNNING' and str(previous['after']['id']) == VM_ID
    folder = trace/'settled-cache-recovery-boot-v3'
    folder.mkdir(exist_ok=False)
    runner.VM = VM

    class Guard(runner.Control):
        def cloud(self, args, **kwargs):
            assert args[:3] in (['compute', 'instances', 'describe'], ['compute', 'instances', 'start'])
            assert args[3] == VM
            return super().cloud(args, **kwargs)

    control = Guard(folder)

    def describe(expected):
        _, out, _ = control.cloud(['compute', 'instances', 'describe', VM,
            '--format=json(name,id,status,zone,machineType,networkInterfaces)'])
        state = json.loads(out)
        assert state['name'] == VM and str(state['id']) == VM_ID and state['status'] == expected
        assert state['zone'].rsplit('/', 1)[-1] == 'us-central1-a'
        assert state['machineType'].rsplit('/', 1)[-1] == 'e2-highmem-8'
        assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
        return state

    before = describe('TERMINATED')
    with (folder/'boot-once.json').open('x', encoding='utf-8') as stream:
        json.dump(dict(before=before, purpose='Continue audited settled-cache recovery for Full109 trace',
                       compiler_authorized=False, recovery_replay_authorized=False), stream, indent=2)
    control.authenticated = True
    control.cloud(['compute', 'instances', 'start', VM])
    after = describe('RUNNING')
    result = dict(after=after, compiler_invoked=False, other_vm_modified=False, launch_clearance=False)
    (folder/'boot-result.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(folder), state=after['status'])), flush=True)


if __name__ == '__main__':
    main()
