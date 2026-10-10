"""Verify all small-object plan rows and applied receipts against pinned prior scope."""
import json
import sys
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02_full109 import OUTPUT
from prepare_builder02_full107 import OUTPUT as PRIOR

HERE = Path(__file__).parent
BASELINE_REVIEW_SHA = '14532AA9BF8EC20D6CF1B90934FDF481EB3B90B35AD8B310419F6C03E48A813D'


def main(action, number):
    assert action in ('plan', 'receipt') and number in range(3, 9)
    derivation = json.loads((HERE/'full109-small-cache-recovery-control-derivation-v3-v8.json').read_bytes())
    scope = next(row for row in derivation['scopes'] if row['scope'] == number)
    control = next(row for row in scope['records'] if row['target'].startswith('full109_storage_'))
    assert digest(HERE/control['target']) == control['target_sha256']
    remote = '/home/dfredriksen_quantyra_org/full109-storage-cache-repoint-v'+str(number)
    ops = {}
    for path in (OUTPUT/'cache-repoint-controls').glob('*/operation.json'):
        op = json.loads(path.read_bytes())
        if op['remote_control'] == remote and op['action'] in ('plan', 'execute'):
            assert op['action'] not in ops
            assert digest(op['local_result']) == op['result_sha256']
            assert op['control_sha256'] == control['target_sha256']
            ops[op['action']] = op
    assert 'plan' in ops
    plan = json.loads(Path(ops['plan']['local_result']).read_bytes())
    settled = OUTPUT.parent/scope['resource']
    marker = json.loads((settled/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    native = json.loads((check/'terminal-custody.json').read_bytes())
    stop = json.loads((check/'vm-termination.json').read_bytes())
    assert marker['run'] == native['run'] == stop['run'] == scope['run']
    assert native['terminal']['native_terminal'] and stop['custody_verified_before_stop']
    assert str(stop['independent']['id']) == '7237681467779354904'
    assert stop['independent']['status'] == 'TERMINATED'
    custody = native['custody']
    assert custody['remote_sha256'] == scope['native_archive_sha256']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert digest(settled/'capture-manifest.json') == scope['manifest_sha256']
    assert plan['old_root'] == '/home/dfredriksen_quantyra_org/'+scope['run']+'/.lake/packages'
    assert plan['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
    assert plan['original_archive_sha256'] == scope['native_archive_sha256']
    assert plan['hash_or_size_mismatches_skipped'] == 0
    assert not plan['executed'] and not plan['compiler_invoked']
    review_path = PRIOR/'consumption-v3/complete-trace-cache-plan-review-v1-v4-v8.json'
    assert digest(review_path) == BASELINE_REVIEW_SHA
    baseline_op = next(row for row in json.loads(review_path.read_bytes())['plans'] if row['scope'] == 4)['operation']
    assert digest(baseline_op['local_result']) == baseline_op['result_sha256']
    baseline = json.loads(Path(baseline_op['local_result']).read_bytes())
    index = {row['relative']: row for row in baseline['rows']}
    assert len(index) == len(baseline['rows']) == len(plan['rows']) == 19233
    seen = set()
    for row in plan['rows']:
        assert row['relative'] not in seen
        seen.add(row['relative'])
        assert row == index[row['relative']], 'Complete row differs from fully audited canonical scope'
    assert seen == set(index)
    assert sum(row['allocated_bytes'] for row in plan['rows']) == plan['allocated_bytes'] >= scope['target_bytes']
    result = dict(schema='full109-small-cache-'+action+'-audit-v1', scope=number, run=scope['run'],
                  rows=19233, plan_sha256=ops['plan']['result_sha256'], all_rows_match_prior_pinned_scope=True,
                  canonical_sources_and_project_objects_excluded=True,
                  identity_level='Current old/canonical byte equality, not exhaustive capture-time cache hashes',
                  compiler_invoked=False, accepted=False)
    if action == 'receipt':
        assert 'execute' in ops
        receipt = json.loads(Path(ops['execute']['local_result']).read_bytes())
        assert receipt['applied'] == plan['rows']
        assert receipt['content_identity_verified_after_repoint']
        assert receipt['reversible_by_copying_identical_canonical_bytes']
        for key in ['warm_files_written', 'source_or_project_object_files_changed', 'failed_evidence_archive_changed', 'compiler_invoked']:
            assert receipt[key] is False
        assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
        result.update(receipt_sha256=ops['execute']['result_sha256'], disk_after_bytes=receipt['disk_after_bytes'])
    path = OUTPUT/('storage-'+action+'-complete-audit-v'+str(number)+'.json')
    data = (json.dumps(result, indent=2)+'\n').encode()
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)
    print(json.dumps(result))


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]))
