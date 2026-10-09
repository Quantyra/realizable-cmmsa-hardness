"""Complete plan and applied-row verification for settled duplicate recovery."""
import json
import re
import sys
from pathlib import Path, PurePosixPath
from custody_checks import digest
from full103_consumption_v2_controller import ROOT as OUTPUT
from derive_full103_trace_cache_recovery import SCOPES
TARGETS = [5,5]

HERE = Path(__file__).parent


def operations(number):
    result = {}
    remote = '/home/dfredriksen_quantyra_org/full103-trace-cache-repoint-v'+str(number)
    for path in (OUTPUT/'cache-repoint-controls').glob('*/operation.json'):
        op = json.loads(path.read_bytes())
        if op['remote_control'] == remote and op['action'] in ('plan','execute'):
            assert op['action'] not in result
            assert digest(op['local_result']) == op['result_sha256']
            result[op['action']] = op
    return result


def plan_review():
    baseline_root = OUTPUT.parent.parent/'full102-spectral-owned-warning-repair-resource02'
    baseline_record = json.loads((baseline_root/'storage-plan-complete-review-v1.json').read_bytes())['plans'][0]
    baseline_path = Path(baseline_record['plan_path'])
    assert digest(baseline_path) == baseline_record['plan_sha256']
    baseline = json.loads(baseline_path.read_bytes())
    index = {row['relative']:row for row in baseline['rows']}
    assert len(index) == len(baseline['rows']) == 9672
    records = []
    for number, resource in enumerate(SCOPES, 1):
        ops = operations(number); assert 'plan' in ops
        op = ops['plan']; plan = json.loads(Path(op['local_result']).read_bytes())
        parent = OUTPUT.parent.parent/resource
        marker = json.loads((parent/'launch-once.json').read_bytes())
        terminal = json.loads((Path(marker['preflight'])/'terminal-custody.json').read_bytes())
        assert plan['old_root'] == '/home/dfredriksen_quantyra_org/'+marker['run']+'/.lake/packages'
        assert plan['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
        assert plan['original_archive_sha256'] == terminal['custody']['remote_sha256']
        assert plan['hash_or_size_mismatches_skipped'] == 0
        assert not plan['executed'] and not plan['compiler_invoked']
        assert op['control_sha256'] == digest(HERE/('full103_trace_cache_repoint_v'+str(number)+'.py'))
        seen = set(); allocation = 0
        for row in plan['rows']:
            assert set(row) == {'relative','sha256','bytes','allocated_bytes'}
            rel = PurePosixPath(row['relative'])
            assert not rel.is_absolute() and all(p not in ('','.','..') for p in rel.parts)
            assert '/.lake/build/lib/lean/' in '/'+row['relative']
            assert rel.name.endswith(('.olean','.olean.private','.olean.server','.ilean'))
            assert row['relative'] not in seen; seen.add(row['relative'])
            assert re.fullmatch('[A-F0-9]{64}',row['sha256'])
            assert type(row['bytes']) is int and row['bytes'] >= 65536
            assert type(row['allocated_bytes']) is int and row['allocated_bytes'] > 0 and row['allocated_bytes'] % 512 == 0
            assert row == index[row['relative']], 'Each full row must equal prior fully reviewed canonical scope'
            allocation += row['allocated_bytes']
        assert allocation == plan['allocated_bytes'] >= TARGETS[number-1]*1024**3
        assert seen == set(index)
        records.append(dict(scope=number,run=marker['run'],plan_path=op['local_result'],
            plan_sha256=op['result_sha256'],control_sha256=op['control_sha256'],rows=len(seen),
            allocated_bytes=allocation,all_rows_reviewed=True,zero_hash_or_size_mismatches=True))
    result = dict(schema='full103-trace-complete-two-plan-row-review-v1-v2',plans=records,
        current_trace_and_canonical_sources_and_project_objects_excluded=True,
        identity_level='Current per-file old/canonical hash and size equality; no exhaustive capture-time cache identity claim',
        executed=False,accepted=False)
    data = (json.dumps(result,indent=2)+'\n').encode()
    out = OUTPUT/'trace-storage-plan-complete-review-v1-v2.json'
    if out.exists(): assert out.read_bytes() == data
    else: out.write_bytes(data)
    (HERE/'full103-trace-storage-plan-complete-review-v1-v2.json').write_bytes(data)
    print(json.dumps(dict(plans=records,review_sha256=digest(out))))


def receipt_review(number):
    assert number in (1,2)
    reviewed = json.loads((OUTPUT/'trace-storage-plan-complete-review-v1-v2.json').read_bytes())['plans'][number-1]
    ops = operations(number); assert set(ops) == {'plan','execute'}
    assert reviewed['plan_sha256'] == ops['plan']['result_sha256']
    assert reviewed['control_sha256'] == ops['plan']['control_sha256'] == ops['execute']['control_sha256']
    plan = json.loads(Path(ops['plan']['local_result']).read_bytes())
    receipt = json.loads(Path(ops['execute']['local_result']).read_bytes())
    assert receipt['applied'] == plan['rows'] and len(receipt['applied']) == reviewed['rows']
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    for name in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'):
        assert receipt[name] is False
    assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
    result = dict(schema='full103-trace-complete-execution-receipt-audit-v1',scope=number,
        operation=ops['execute'],plan_sha256=ops['plan']['result_sha256'],rows_exact=reviewed['rows'],
        allocation=reviewed['allocated_bytes'],disk_after_bytes=receipt['disk_after_bytes'],
        content_and_reversibility_preserved=True,compiler_invoked=False,accepted=False)
    data = (json.dumps(result,indent=2)+'\n').encode()
    out = OUTPUT/('recovery-receipt-audit-v'+str(number)+'.json')
    if out.exists(): assert out.read_bytes() == data
    else: out.write_bytes(data)
    print(json.dumps(dict(scope=number,rows=reviewed['rows'],disk_after_bytes=receipt['disk_after_bytes'],
        receipt_sha256=ops['execute']['result_sha256'],audit_sha256=digest(out))))


if __name__ == '__main__':
    if sys.argv[1:] == ['plan']: plan_review()
    elif len(sys.argv) == 3 and sys.argv[1] == 'receipt': receipt_review(int(sys.argv[2]))
    else: raise SystemExit('Use plan or receipt NUMBER')
