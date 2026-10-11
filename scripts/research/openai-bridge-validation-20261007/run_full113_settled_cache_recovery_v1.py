"""One retained controller for selected settled-cache operations; no Lean execution."""
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from custody_checks import digest, verify_local_custody
from full113_builder02_controller import ROOT, VM, VM_ID, context, local_gates
from full113_capture_gates import validate_successor

HERE = Path(__file__).resolve().parent
NEXT = ROOT.parent / 'full114-exact-real-complex-operators-repair4-resource02'


def settled():
    validate_successor()
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    assert marker['run'] == receipt['run'] == stop['run'] == 'cmmsa_a8_output_20261011T060110Z_204d10cd'
    assert receipt['terminal']['native_terminal'] and stop['custody_verified_before_stop']
    assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == VM_ID
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert not (NEXT / 'launch-once.json').exists()
    return stop


def main(action, numbers):
    assert action == 'boot', 'This derived control is admitted only for the once-guarded boot'
    settled()
    loaded, runner = context()
    local_gates(loaded['common'], loaded)
    runner.VM = VM
    root = ROOT / 'settled-cache-recovery-v1'
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder = root / stamp
    folder.mkdir(parents=True, exist_ok=False)
    control = runner.Control(folder)
    _, raw, _ = control.cloud(['compute', 'instances', 'describe', VM,
        '--format=json(name,id,status,zone,machineType,networkInterfaces)'])
    state = json.loads(raw)
    assert state['name'] == VM and str(state['id']) == VM_ID
    assert state['zone'].rsplit('/', 1)[-1] == 'us-central1-a'
    assert state['machineType'].rsplit('/', 1)[-1] == 'e2-highmem-8'
    assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
    control.authenticated = True
    if action == 'boot':
        assert not numbers and state['status'] == 'TERMINATED'
        (root / 'boot-once.json').open('x', encoding='utf-8').write(json.dumps(dict(before=state, control=str(folder)))+'\n')
        control.cloud(['compute', 'instances', 'start', VM])
        _, raw, _ = control.cloud(['compute', 'instances', 'describe', VM,
            '--format=json(name,id,status,zone,machineType,networkInterfaces)'])
        after = json.loads(raw)
        assert after['name'] == VM and str(after['id']) == VM_ID and after['status'] == 'RUNNING'
        assert after['zone'] == state['zone'] and after['machineType'] == state['machineType']
        assert not any(n.get('accessConfigs') for n in after['networkInterfaces'])
        (root / 'boot-result.json').open('x', encoding='utf-8').write(json.dumps(dict(before=state, after=after, control=str(folder), compiler_invoked=False), indent=2)+'\n')
        print(json.dumps(dict(action=action, folder=str(folder), native_exit=0, compiler_invoked=False)), flush=True)
        return
    assert state['status'] == 'RUNNING' and numbers and len(set(numbers)) == len(numbers)
    derivation = json.loads((HERE / 'full113-settled-cache-recovery-derivation-v1.json').read_bytes())
    scopes = {row['number']: row for row in derivation['scopes']}
    assert all(number in scopes for number in numbers)
    results = []
    for number in numbers:
        scope = scopes[number]
        source = HERE / scope['helper']
        assert source.name == f'full113_settled_cache_native{number}_v1.py'
        assert digest(source) == scope['helper_sha256']
        remote = scope['remote_control']
        assert remote == '/home/dfredriksen_quantyra_org/full113-settled-cache-native' + str(number) + '-v1'
        if action == 'plan':
            control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=mkdir ' + remote])
            control.cloud(['compute', 'scp', str(source), VM + ':' + remote + '/', '--tunnel-through-iap'])
        _, raw, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=sha256sum ' + remote + '/' + source.name])
        assert raw.decode().split()[0].upper() == scope['helper_sha256']
        (folder / source.name).open('xb').write(source.read_bytes())
        if action == 'execute':
            candidates = []
            for operation in root.glob('*/operation-*.json'):
                value = json.loads(operation.read_bytes())
                if value['number'] == number and value['action'] in ('plan', 'collect-plan'):
                    candidates.append(value)
            assert candidates and len({row['result_sha256'] for row in candidates}) == 1
            plan = candidates[-1]
            assert digest(Path(plan['local_result'])) == plan['result_sha256']
            _, raw, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=sha256sum ' + remote + '/plan.json'])
            assert raw.decode().split()[0].upper() == plan['result_sha256']
        if action in ('plan', 'execute'):
            code, _, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
                '--command=python3 -B ' + remote + '/' + source.name + ' --' + action], timeout=1200, allow_failure=True)
            assert code == 0, 'Original operation failed; collect existing evidence without replay'
        name = 'plan.json' if action in ('plan', 'collect-plan') else 'receipt.json'
        _, raw, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=sha256sum ' + remote + '/' + name])
        pin = raw.decode().split()[0].upper()
        destination = folder / (str(number) + '-' + name)
        control.cloud(['compute', 'scp', VM + ':' + remote + '/' + name, str(destination), '--tunnel-through-iap'], timeout=300)
        assert digest(destination) == pin
        value = json.loads(destination.read_bytes())
        if name == 'plan.json':
            assert value['original_archive_sha256'] == scope['archive_sha256']
            assert value['old_root'] == '/home/dfredriksen_quantyra_org/' + scope['run'] + '/.lake/packages'
            assert value['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
            rows = value['rows']
            assert rows and len({r['relative'] for r in rows}) == len(rows)
            for row in rows:
                path = Path(row['relative'])
                assert not path.is_absolute() and '..' not in path.parts and row['bytes'] > 0
                assert path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ilean'))
                assert {'.lake', 'build', 'lib', 'lean'} <= set(path.parts)
                assert len(row['sha256']) == 64 and all(c in '0123456789ABCDEF' for c in row['sha256'])
            assert sum(r['allocated_bytes'] for r in rows) == value['allocated_bytes'] >= scope['target_bytes']
        else:
            plan = json.loads(Path(plan['local_result']).read_bytes()) if action == 'execute' else None
            if plan is not None:
                assert value['applied'] == plan['rows']
            assert value['content_identity_verified_after_repoint'] and value['reversible_by_copying_identical_canonical_bytes']
            assert value['disk_after_bytes'] > value['disk_before_bytes']
            assert not any(value[k] for k in ('warm_files_written', 'source_or_project_object_files_changed', 'failed_evidence_archive_changed', 'compiler_invoked'))
        record = dict(action=action, number=number, local_result=str(destination), result_sha256=pin,
            helper_sha256=scope['helper_sha256'], remote_control=remote, compiler_invoked=False, VM_power_operation=False)
        (folder / f'operation-{number}.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
        results.append(record)
        print(json.dumps(record), flush=True)
    local_gates(loaded['common'], loaded)
    print(json.dumps(dict(folder=str(folder), operations=len(results), original_operations_settled=True)), flush=True)


if __name__ == '__main__':
    main(sys.argv[1], [int(value) for value in sys.argv[2:]])
