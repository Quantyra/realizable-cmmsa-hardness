"""Admit scope90's collected receipt only with its preserved original execution."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
function = '''def execution_operation(number):
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


'''
record = []


def derive(source_name, target_name, changes):
    source = HERE / source_name
    text = source.read_text(encoding='utf-8')
    for old, new, count in changes:
        assert text.count(old) == count, (source_name, old)
        text = text.replace(old, new)
    ast.parse(text)
    target = HERE / target_name
    target.open('xb').write(text.encode('utf-8'))
    record.append(dict(source=source_name, source_sha256=digest(source), target=target_name,
                       target_sha256=digest(target), exact_replacements=changes))


derive('audit_full110_settled_cache_recovery_v1.py', 'audit_full110_settled_cache_recovery_v2.py', [
    ("AUDIT = RECOVERY / 'complete-audit-v1'", "AUDIT = RECOVERY / 'complete-audit-v2'", 1),
    ("unique_operation(number, 'execute')", 'execution_operation(number)', 2),
    ('def validate_local_audit():', function + 'def validate_local_audit():', 1),
    ("'full110-all-seven-recovery-journal-audit-v1'", "'full110-all-seven-recovery-journal-audit-v2'", 1),
    ("    AUDIT.mkdir(exist_ok=False)", """    failure_index = HERE / 'full110-recovery-execution-interruption-v1/index.json'
    failure = json.loads(failure_index.read_bytes())
    assert failure['original_handle'] == 50622 and failure['original_exit'] == 1
    register(failure_index)
    for row in failure['files']:
        path = failure_index.parent / row['copy']
        assert digest(path) == row['sha256']
        register(path)
    AUDIT.mkdir(exist_ok=False)""", 1)])
derive('stage_full111_after_recovery_v1.py', 'stage_full111_after_recovery_v2.py', [
    ('from audit_full110_settled_cache_recovery_v1 import',
     'from audit_full110_settled_cache_recovery_v2 import', 1)])
derive('run_full111_resume_step_v2.py', 'run_full111_resume_step_v3.py', [
    ('stage_full111_after_recovery_v1.py', 'stage_full111_after_recovery_v2.py', 1),
    ('audit_full110_settled_cache_recovery_v1.py', 'audit_full110_settled_cache_recovery_v2.py', 1)])
(HERE / 'full111-collected-recovery-admission-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(dict(
    records=record, preserved_original_controller_exit=1, scope90_native_execution_exit=0,
    scope90_receipt_collection_only=True, unchanged_complete_plan_receipt_journal_checks=True,
    audit_or_staging_or_compiler_executed=False), indent=2)+'\n')
print(json.dumps(dict(derived_controls=3, scope90_original_execution_required=True, no_execution_replay=True)))
