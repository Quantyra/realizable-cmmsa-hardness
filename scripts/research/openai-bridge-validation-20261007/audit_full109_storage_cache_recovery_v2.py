"""Audit every settled Full108 duplicate-cache plan row and applied receipt."""
import json
import sys
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02_full109 import OUTPUT
from prepare_builder02_full105 import OUTPUT as SETTLED
from prepare_builder02_full107 import OUTPUT as PRIOR

HERE = Path(__file__).parent
REMOTE = '/home/dfredriksen_quantyra_org/full109-storage-cache-repoint-v2'


def operations():
    result = {}
    for path in (OUTPUT/'cache-repoint-controls').glob('*/operation.json'):
        op = json.loads(path.read_bytes())
        if op['remote_control'] == REMOTE and op['action'] in ('plan', 'execute'):
            assert op['action'] not in result
            assert digest(op['local_result']) == op['result_sha256']
            assert op['control_sha256'] == digest(HERE/'full109_storage_cache_repoint_v2.py')
            result[op['action']] = op
    return result


def main(action):
    assert action in ('plan', 'receipt')
    ops = operations()
    assert 'plan' in ops
    plan = json.loads(Path(ops['plan']['local_result']).read_bytes())
    marker = json.loads((SETTLED/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    native = json.loads((check/'terminal-custody.json').read_bytes())
    stop = json.loads((check/'vm-termination.json').read_bytes())
    assert marker['run'] == native['run'] == stop['run']
    assert native['terminal']['native_terminal'] and stop['custody_verified_before_stop']
    assert str(stop['independent']['id']) == '7237681467779354904'
    assert stop['independent']['status'] == 'TERMINATED'
    custody = native['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert plan['old_root'] == '/home/dfredriksen_quantyra_org/'+marker['run']+'/.lake/packages'
    assert plan['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
    assert plan['original_archive_sha256'] == custody['remote_sha256']
    assert not plan['executed'] and not plan['compiler_invoked']
    assert plan['hash_or_size_mismatches_skipped'] == 0
    baseline_record = json.loads((PRIOR/'trace-storage-plan-complete-review-v1-v3.json').read_bytes())['plans'][0]
    assert digest(baseline_record['plan_path']) == baseline_record['plan_sha256']
    baseline = json.loads(Path(baseline_record['plan_path']).read_bytes())
    index = {row['relative']: row for row in baseline['rows']}
    assert len(index) == len(baseline['rows']) == 9672
    assert len(plan['rows']) == len(index)
    seen = set()
    for row in plan['rows']:
        assert row['relative'] not in seen
        seen.add(row['relative'])
        assert row == index[row['relative']], 'Complete row must match previously reviewed canonical scope'
    assert seen == set(index)
    assert sum(row['allocated_bytes'] for row in plan['rows']) == plan['allocated_bytes'] >= 5*1024**3
    result = dict(schema='full109-complete-settled-cache-'+action+'-audit-v2',
                  run=marker['run'], rows=9672, plan_sha256=ops['plan']['result_sha256'],
                  original_native_archive_sha256=custody['remote_sha256'],
                  canonical_sources_and_project_objects_excluded=True,
                  identity_level='Current old/canonical per-file byte equality, not exhaustive capture-time cache hashes',
                  compiler_invoked=False, accepted=False)
    if action == 'receipt':
        assert 'execute' in ops
        receipt = json.loads(Path(ops['execute']['local_result']).read_bytes())
        assert receipt['applied'] == plan['rows']
        assert receipt['content_identity_verified_after_repoint']
        assert receipt['reversible_by_copying_identical_canonical_bytes']
        for field in ['warm_files_written', 'source_or_project_object_files_changed', 'failed_evidence_archive_changed', 'compiler_invoked']:
            assert receipt[field] is False
        assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
        result.update(receipt_sha256=ops['execute']['result_sha256'], disk_after_bytes=receipt['disk_after_bytes'])
    path = OUTPUT/('storage-'+action+'-complete-audit-v2.json')
    data = (json.dumps(result, indent=2)+'\n').encode()
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)
    print(json.dumps(result))


if __name__ == '__main__':
    main(sys.argv[1])
