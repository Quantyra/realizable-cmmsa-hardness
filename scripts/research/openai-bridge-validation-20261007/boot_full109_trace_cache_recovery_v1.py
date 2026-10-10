"""One authorized exact-VM boot for inspecting interrupted recovery; no replay."""
import json
from full109_builder02_controller import ROOT, VM, VM_ID, context, local_gates
from full109_capture_gates import validate_successor

def main():
    validate_successor()
    loaded, runner = context()
    local_gates(loaded['common'], loaded)
    assert not (ROOT/'consumption-v3'/'launch-once.json').exists()
    folder = ROOT/'consumption-v3'/'settled-cache-recovery-boot-v1'
    folder.mkdir(exist_ok=False)
    runner.VM = VM
    class Guard(runner.Control):
        def cloud(self, args, **kwargs):
            assert args[:3] in (['compute','instances','describe'], ['compute','instances','start'])
            assert args[3] == VM
            return super().cloud(args, **kwargs)
    control = Guard(folder)
    def describe(expected):
        _, out, _ = control.cloud(['compute','instances','describe',VM,
            '--format=json(name,id,status,zone,machineType,networkInterfaces)'])
        state = json.loads(out)
        assert state['name'] == VM and str(state['id']) == VM_ID
        assert state['status'] == expected
        assert state['zone'].rsplit('/',1)[-1] == 'us-central1-a'
        assert state['machineType'].rsplit('/',1)[-1] == 'e2-highmem-8'
        assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
        return state
    before = describe('TERMINATED')
    with (folder/'boot-once.json').open('x') as stream:
        json.dump(dict(before=before, purpose='Qualified trace settled-cache recovery after verified termination',
            compiler_authorized=False, recovery_replay_authorized=False), stream, indent=2)
    control.authenticated = True
    control.cloud(['compute','instances','start',VM])
    after = describe('RUNNING')
    (folder/'boot-result.json').write_text(json.dumps(dict(after=after,
        compiler_invoked=False, other_vm_modified=False, launch_clearance=False), indent=2)+'\n')
    print(json.dumps(dict(folder=str(folder), state=after['status'])), flush=True)

if __name__ == '__main__':
    main()
