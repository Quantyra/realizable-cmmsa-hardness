"""Require all six complete receipts, preserving original transport failures."""
import base64
import hashlib
import json
from pathlib import Path
from audit_full109_trace_cache_small_v1 import main as audit
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
TRACE = ROOT/'consumption-v3'
PIN89 = '17BDA840557AB015CD086F91E18D68CFB078343779521C57BF2A273F90EA64BA'


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    assert not (TRACE/'launch-once.json').exists()
    audit('plan', 84)
    preserved84 = HERE/'full109-resume-native84-received-custody-v1'
    prior84 = read(preserved84/'index.json')
    assert prior84['original_native_exit'] == 1 and prior84['original_execution_command_native_exit'] == 0
    assert prior84['complete_actual_row_identity_verified'] and prior84['rows'] == 19233
    for row in prior84['files']:
        assert digest(row['original']) == digest(preserved84/row['copy']) == row['sha256']
    scopes = [dict(scope=84, original_controller_native_exit=1, original_execution_native_exit=0,
                   rows=19233, receipt_sha256=prior84['settled_received_receipt_sha256'],
                   audit_sha256=digest(preserved84/'index.json'))]
    for number in range(85,89):
        audit('receipt', number)
        path = TRACE/f'cache-small-receipt-audit-native{number}-v1.json'
        value = read(path)
        assert value['rows'] == 19233
        scopes.append(dict(scope=number, original_controller_native_exit=0, original_execution_native_exit=0,
                           rows=19233, receipt_sha256=value['receipt_sha256'], audit_sha256=digest(path)))
    audit('plan', 89)
    derivation = read(HERE/'full109-native89-receipt-collector-derivation-v1.json')
    assert digest(HERE/'collect_full109_native89_receipt_v1.py') == derivation['successor_sha256']
    failed = TRACE/'cache-repoint-controls/20261011T001909531238Z'
    wrapper = ROOT/'research-resume-20261010/20261011T001754489124Z'
    assert digest(failed/'commands.json') == derivation['original_commands_sha256']
    assert digest(wrapper/'command.json') == derivation['original_wrapper_sha256']
    assert [c['native_exit'] for c in read(failed/'commands.json')] == [0,0,0,0,1]
    assert read(wrapper/'command.json')['native_exit'] == 1
    collected = list((ROOT/'readonly-receipt-native89-v1').glob('*/inspection.json'))
    assert len(collected) == 1, 'Need one complete original read-only receipt collection'
    inspection = collected[0]
    commands = read(inspection.parent/'commands.json')
    assert len(commands) == 2 and all(c['native_exit'] == 0 for c in commands)
    for i, command in enumerate(commands):
        for stream in ('stdout','stderr'):
            assert digest(inspection.parent/f'{i}.{stream}') == command[stream+'_sha256']
    result = read(inspection)
    assert result == read(inspection.parent/'1.stdout')
    assert result['read_only'] and not result['execution_replayed'] and not result['compiler_invoked']
    raw = base64.b64decode(result['raw_receipt_base64'],validate=True)
    assert hashlib.sha256(raw).hexdigest().upper() == result['receipt_sha256'] == PIN89
    receipt = json.loads(raw)
    operations = [read(p) for p in (TRACE/'cache-repoint-controls').glob('*/operation.json')]
    plan_op = next(p for p in operations if p['action'] == 'plan' and p['remote_control'].endswith('native89-v1'))
    plan = read(plan_op['local_result'])
    assert receipt['applied'] == plan['rows'] and len(receipt['applied']) == 19233
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    for key in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'):
        assert receipt[key] is False
    assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
    target = inspection.parent/'decoded-receipt.json'
    target.open('xb').write(raw)
    scopes.append(dict(scope=89, original_controller_native_exit=1, original_execution_native_exit=0,
                       readonly_collection_native_exit=0, rows=19233, receipt_sha256=PIN89,
                       collection_inspection=str(inspection), collection_inspection_sha256=digest(inspection)))
    assert sum(row['rows'] for row in scopes) == 115398
    value = dict(schema='full109-six-complete-trace-recovery-receipts-v4', scopes=scopes,
                 all115398_actual_rows_verified=True, all_original_remote_recovery_executions_native_exit0=True,
                 original_scope84_and89_transport_native_exit1_retained=True,
                 original_recovery_replayed=False, source_project_objects_and_canonical_cache_excluded=True,
                 trace_executed=False, fresh_authenticated_remote_prelaunch_still_required=True,
                 accepted=False, full_goal_complete=False)
    (TRACE/'complete-trace-recovery-v4.json').open('x',encoding='utf-8').write(json.dumps(value,indent=2)+'\n')
    print(json.dumps(value))


if __name__ == '__main__':
    main()
