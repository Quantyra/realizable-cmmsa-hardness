"""Record exact dedicated02 cache-repoint plan/execution; no VM start or Lean."""
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import sys
from full99_builder02_controller import ROOT, VM, VM_ID, context, local_gates
from full99_capture_gates import validate_successor
from custody_checks import digest

REMOTE = '/home/dfredriksen_quantyra_org/full99-cache-repoint-v1'


def main(action):
    if action not in ('plan', 'execute', 'collect-plan', 'collect-receipt'):
        raise ValueError('Use plan, execute, collect-plan or collect-receipt')
    validate_successor()
    loaded, runner = context()
    local_gates(loaded['common'], loaded)
    if (ROOT / 'launch-once.json').exists():
        raise RuntimeError('Full99 launch exists; no cache operation permitted')
    folder = ROOT / 'cache-repoint-controls' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True)
    runner.VM = VM
    control = runner.Control(folder)
    _, out, _ = control.cloud(['compute', 'instances', 'describe', VM,
                              '--format=json(name,id,status,zone,networkInterfaces)'])
    state = json.loads(out)
    if state['name'] != VM or str(state['id']) != VM_ID or state['status'] != 'RUNNING' or state['zone'].rsplit('/', 1)[-1] != 'us-central1-a':
        raise RuntimeError('Unexpected dedicated02 state')
    if any(nic.get('accessConfigs') for nic in state['networkInterfaces']):
        raise RuntimeError('Unexpected external IP')
    # The successful exact-identity SDK describe is the authenticated
    # preflight required by the preserved transport controller.
    control.authenticated = True
    source = Path(__file__).with_name('full99_cache_repoint_v1.py')
    pin = digest(source)
    if action == 'plan':
        control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=mkdir ' + REMOTE])
        control.cloud(['compute', 'scp', str(source), VM + ':' + REMOTE + '/', '--tunnel-through-iap'])
    _, out, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
                              '--command=sha256sum ' + REMOTE + '/' + source.name])
    if out.decode().split()[0].upper() != pin:
        raise RuntimeError('Repoint control drift')
    with (folder / 'executed-repoint-control.py').open('xb') as stream:
        stream.write(source.read_bytes())
    if action in ('plan', 'execute'):
        code, out, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
                                     '--command=python3 -B ' + REMOTE + '/' + source.name + ' --' + action],
                                    timeout=600, allow_failure=True)
        if code:
            raise RuntimeError('Same cache-repoint operation failed; preserve and inspect ' + str(folder))
    name = 'plan.json' if action in ('plan', 'collect-plan') else 'receipt.json'
    # Large JSON stdout crashed the Windows SSH client after a successful
    # planning operation. Retrieve the existing file, without repeating it.
    _, raw, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
                              '--command=sha256sum ' + REMOTE + '/' + name])
    expected_pin = raw.decode().split()[0].upper()
    control.cloud(['compute', 'scp', VM + ':' + REMOTE + '/' + name,
                   str(folder / name), '--tunnel-through-iap'], timeout=300)
    if digest(folder / name) != expected_pin:
        raise RuntimeError('Retrieved JSON identity mismatch')
    value = json.loads((folder / name).read_bytes())
    receipt = {'action': action, 'VM': state, 'control_sha256': pin, 'remote_control': REMOTE,
               'local_result': str(folder / name), 'result_sha256': digest(folder / name),
               'compiler_invoked': False, 'VM_power_operation': False, 'accepted': False}
    with (folder / 'operation.json').open('x', encoding='utf-8') as stream:
        json.dump(receipt, stream, indent=2)
    local_gates(loaded['common'], loaded)
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
