"""Collect complete journals and independently reconcile all seven settled scopes."""
import base64
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from custody_checks import digest
from full110_builder02_controller import ROOT, VM, VM_ID, context, local_gates
from run_full110_settled_cache_recovery_v1 import settled

HERE = Path(__file__).resolve().parent
RECOVERY = ROOT / 'settled-cache-recovery-v1'
AUDIT = RECOVERY / 'complete-audit-v2'
NUMBERS = [110, 90, 91, 92, 93, 94, 95]


def unique_operation(number, action):
    rows = []
    for path in RECOVERY.glob('*/operation-*.json'):
        row = json.loads(path.read_bytes())
        if row['number'] == number and row['action'] == action:
            assert digest(Path(row['local_result'])) == row['result_sha256']
            rows.append((path, row))
    assert len(rows) == 1, (number, action, len(rows))
    return rows[0]


def execution_operation(number):
    if number != 90:
        return unique_operation(number, 'execute')
    original = RECOVERY / '20261011T033104479357Z'
    wrapper = ROOT / 'research-resume-20261011/20261011T032930698566Z-1587aaca7c15'
    command = json.loads((wrapper / 'command.json').read_bytes())
    assert command['native_exit'] == 1 and command['pid'] == 12852
    for stream in ('stdout', 'stderr'):
        assert digest(wrapper / stream) == command[stream + '_sha256']
    commands = json.loads((original / 'commands.json').read_bytes())
    assert len(commands) == 10
    assert [row['native_exit'] for row in commands] == [0] * 9 + [3221225477]
    for row in commands:
        assert not row['timed_out']
        for stream in ('stdout', 'stderr'):
            assert digest(original / row[stream + '_path']) == row[stream + '_sha256']
    assert commands[8]['argv'][5] == '--command=python3 -B /home/dfredriksen_quantyra_org/full110-settled-cache-native90-v1/full110_settled_cache_native90_v1.py --execute'
    assert commands[9]['argv'][5] == '--command=sha256sum /home/dfredriksen_quantyra_org/full110-settled-cache-native90-v1/receipt.json'
    terminal = json.loads((original / 'control/008.stdout').read_bytes())
    assert terminal['repointed_files'] == 19233 and not terminal['compiler_invoked']
    assert terminal['receipt_sha256'] == '18722833D18CC01D6C14D35ED74424B1E872C98576A87F62E62BEBD1BA5386CE'
    assert not (original / 'operation-90.json').exists()
    path, collected = unique_operation(90, 'collect-receipt')
    assert collected['result_sha256'] == terminal['receipt_sha256']
    assert json.loads(Path(collected['local_result']).read_bytes())['disk_after_bytes'] == terminal['disk_after_bytes']
    return path, collected


def validate_local_audit():
    report = json.loads((AUDIT / 'audit.json').read_bytes())
    assert report['numbers'] == NUMBERS and report['all_rows_match']
    assert report['disk_available_bytes'] >= 40 * 1024**3
    assert not report['compiler_invoked'] and not report['power_operation']
    for row in report['files']:
        path = Path(row['path'])
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    for number in NUMBERS:
        unique_operation(number, 'plan')
        execution_operation(number)
    return report


def main():
    settled()
    loaded, runner = context()
    local_gates(loaded['common'], loaded)
    scopes = json.loads((HERE / 'full110-settled-cache-recovery-derivation-v1.json').read_bytes())['scopes']
    assert [row['number'] for row in scopes] == NUMBERS
    files, reconciled = [], []

    def register(path):
        path = Path(path)
        files.append(dict(path=str(path), bytes=path.stat().st_size, sha256=digest(path)))

    for path in (Path(__file__).resolve(), HERE / 'full110-settled-cache-recovery-derivation-v1.json',
                 RECOVERY / 'boot-once.json', RECOVERY / 'boot-result.json'):
        register(path)
    for scope in scopes:
        number = scope['number']
        pp, pr = unique_operation(number, 'plan')
        ep, er = execution_operation(number)
        plan = json.loads(Path(pr['local_result']).read_bytes())
        receipt = json.loads(Path(er['local_result']).read_bytes())
        assert receipt['applied'] == plan['rows'] and plan['rows']
        assert len({row['relative'] for row in plan['rows']}) == len(plan['rows'])
        assert plan['original_archive_sha256'] == scope['archive_sha256']
        assert sum(row['allocated_bytes'] for row in plan['rows']) == plan['allocated_bytes'] >= scope['target_bytes']
        assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
        assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
        assert not any(receipt[key] for key in ('warm_files_written', 'source_or_project_object_files_changed',
                                               'failed_evidence_archive_changed', 'compiler_invoked'))
        assert pr['helper_sha256'] == er['helper_sha256'] == scope['helper_sha256']
        assert digest(HERE / scope['helper']) == scope['helper_sha256']
        for path in (pp, ep, pr['local_result'], er['local_result'], HERE / scope['helper']):
            register(path)
        reconciled.append(dict(number=number, rows=len(plan['rows']), allocated_bytes=plan['allocated_bytes'],
                               plan_sha256=pr['result_sha256'], receipt_sha256=er['result_sha256']))
    failure_index = HERE / 'full110-recovery-execution-interruption-v1/index.json'
    failure = json.loads(failure_index.read_bytes())
    assert failure['original_handle'] == 50622 and failure['original_exit'] == 1
    register(failure_index)
    for row in failure['files']:
        path = failure_index.parent / row['copy']
        assert digest(path) == row['sha256']
        register(path)
    AUDIT.mkdir(exist_ok=False)
    runner.VM = VM
    control = runner.Control(AUDIT)
    _, raw, _ = control.cloud(['compute', 'instances', 'describe', VM,
        '--format=json(name,id,status,zone,machineType,networkInterfaces)'])
    state = json.loads(raw)
    assert state['name'] == VM and str(state['id']) == VM_ID and state['status'] == 'RUNNING'
    assert state['zone'].rsplit('/', 1)[-1] == 'us-central1-a'
    assert state['machineType'].rsplit('/', 1)[-1] == 'e2-highmem-8'
    assert not any(nic.get('accessConfigs') for nic in state['networkInterfaces'])
    control.authenticated = True
    guest = '''import base64, hashlib, importlib.util, json, shutil
from pathlib import Path
scopes = SCOPES
rows = []
for scope in scopes:
    root = Path(scope['remote_control'])
    helper = root / scope['helper']
    assert hashlib.sha256(helper.read_bytes()).hexdigest().upper() == scope['helper_sha256']
    spec = importlib.util.spec_from_file_location('recovery_guard', helper)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.guards()
    captured = {}
    for name in ('execution-journal.jsonl', 'execute-once.json'):
        data = (root / name).read_bytes()
        captured[name] = dict(base64=base64.b64encode(data).decode(), bytes=len(data),
                             sha256=hashlib.sha256(data).hexdigest().upper())
    rows.append(dict(number=scope['number'], files=captured))
print(json.dumps(dict(scopes=rows, disk_available_bytes=shutil.disk_usage('/home/dfredriksen_quantyra_org').free,
                     original_archive_source_terminal_and_quiescence_guards_passed=True,
                     compiler_invoked=False, power_operation=False)))
'''.replace('SCOPES', repr([{key: row[key] for key in ('number', 'remote_control', 'helper', 'helper_sha256')}
                            for row in scopes]))
    (AUDIT / 'guest-read-only.py').open('xb').write(guest.encode('utf-8'))
    encoded = base64.b64encode(guest.encode()).decode()
    command = 'python3 -B -c "import base64;exec(base64.b64decode(\'' + encoded + '\'))"'
    _, raw, _ = control.cloud(['compute', 'ssh', VM, '--tunnel-through-iap', '--command=' + command], timeout=1200)
    observation = json.loads(raw)
    assert [row['number'] for row in observation['scopes']] == NUMBERS
    assert observation['original_archive_source_terminal_and_quiescence_guards_passed']
    for row, summary in zip(observation['scopes'], reconciled):
        decoded = {}
        for name, record in row['files'].items():
            data = base64.b64decode(record['base64'], validate=True)
            assert len(data) == record['bytes'] and hashlib.sha256(data).hexdigest().upper() == record['sha256']
            path = AUDIT / (str(row['number']) + '-' + name)
            path.open('xb').write(data)
            register(path)
            decoded[name] = data
        _, operation = unique_operation(row['number'], 'plan')
        plan = json.loads(Path(operation['local_result']).read_bytes())
        journal = [json.loads(line) for line in decoded['execution-journal.jsonl'].splitlines()]
        marker = json.loads(decoded['execute-once.json'])
        assert journal == plan['rows']
        assert marker['plan_sha256'] == summary['plan_sha256'] and not marker['compiler_invoked']
        summary['journal_rows'] = len(journal)
    assert observation['disk_available_bytes'] >= 40 * 1024**3
    for path in AUDIT.iterdir():
        if path.is_file() and not any(row['path'] == str(path) for row in files):
            register(path)
    local_gates(loaded['common'], loaded)
    result = dict(schema='full110-all-seven-recovery-journal-audit-v2', utc=datetime.now(timezone.utc).isoformat(),
        numbers=NUMBERS, scopes=reconciled, files=files, all_rows_match=True,
        disk_available_bytes=observation['disk_available_bytes'], state=state,
        original_archive_source_terminal_and_quiescence_guards_passed=True,
        compiler_invoked=False, power_operation=False, mathematical_acceptance=False)
    (AUDIT / 'audit.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    validate_local_audit()
    print(json.dumps(dict(audit=str(AUDIT / 'audit.json'), all_seven_scopes_verified=True,
                         disk_available_bytes=result['disk_available_bytes'])), flush=True)


if __name__ == '__main__':
    main()
