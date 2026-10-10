"""Audit every exact duplicate row and applied receipt before trace launch."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile
from full107_consumption_v3_controller import ROOT
from custody_checks import digest

HERE = Path(__file__).parent
SCOPES = [('full107-exact-product-energy-repair-resource02', 5, 65536),
          ('full106-exact-product-energy-resource02', 2, 1), ('full83-resource02', 2, 1)]


def operation(number, action):
    remote = '/home/dfredriksen_quantyra_org/full107-trace-cache-repoint-v' + str(number)
    matches = []
    for path in (ROOT/'cache-repoint-controls').glob('*/operation.json'):
        value = json.loads(path.read_bytes())
        if value['remote_control'] == remote and value['action'] == action:
            assert digest(value['local_result']) == value['result_sha256']
            matches.append(value)
    assert len(matches) == 1, (number, action)
    return matches[0]


def plan_review():
    records = []
    for number, (scope, target, minimum) in enumerate(SCOPES, 1):
        op = operation(number, 'plan')
        plan = json.loads(Path(op['local_result']).read_bytes())
        parent = ROOT.parent.parent/scope
        marker = json.loads((parent/'launch-once.json').read_bytes())
        check = Path(marker['preflight'])
        receipt = json.loads((check/'terminal-custody.json').read_bytes())
        assert json.loads((check/'vm-termination.json').read_bytes())['independent']['status'] == 'TERMINATED'
        assert plan['old_root'] == '/home/dfredriksen_quantyra_org/'+marker['run']+'/.lake/packages'
        assert plan['canonical_root'] == '/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
        assert plan['original_archive_sha256'] == receipt['custody']['remote_sha256']
        assert not plan['executed'] and not plan['compiler_invoked']
        assert plan['hash_or_size_mismatches_skipped'] == 0
        assert op['control_sha256'] == digest(HERE/f'full107_trace_cache_repoint_v{number}.py')
        with tarfile.open(receipt['custody']['repository_path']) as archive:
            objects = json.loads(archive.extractfile('object-after.json').read())
        seen = set()
        allocation = 0
        for row in plan['rows']:
            assert set(row) == {'relative', 'sha256', 'bytes', 'allocated_bytes'}
            rel = PurePosixPath(row['relative'])
            assert not rel.is_absolute() and all(p not in ('', '.', '..') for p in rel.parts)
            assert '/.lake/build/lib/lean/' in '/'+str(rel)
            assert rel.name.endswith(('.olean', '.olean.private', '.olean.server', '.ilean'))
            assert row['relative'] not in seen
            seen.add(row['relative'])
            assert '.lake/packages/'+str(rel) not in objects
            assert re.fullmatch('[A-F0-9]{64}', row['sha256'])
            assert type(row['bytes']) is int and row['bytes'] >= minimum
            assert type(row['allocated_bytes']) is int and row['allocated_bytes'] > 0
            assert row['allocated_bytes'] % 512 == 0
            allocation += row['allocated_bytes']
        assert allocation == plan['allocated_bytes'] >= target*1024**3
        records.append(dict(scope=number, operation=op, rows=len(seen), allocated_bytes=allocation,
                            all_rows_reviewed=True, original_native_objects_excluded=True))
    result = dict(plans=records, identity_level='Current exact per-file equality; no exhaustive capture-time cache hashing claim', executed=False)
    path = ROOT/'complete-trace-cache-plan-review.json'
    data = (json.dumps(result, indent=2)+'\n').encode()
    if path.exists(): assert path.read_bytes() == data
    else: path.open('xb').write(data)
    print(json.dumps(dict(plans=[dict(scope=r['scope'], rows=r['rows'], allocated_bytes=r['allocated_bytes']) for r in records], review_sha256=digest(path))))


def receipt_review(number):
    assert number in (1, 2, 3)
    reviewed = json.loads((ROOT/'complete-trace-cache-plan-review.json').read_bytes())['plans'][number-1]
    plan_op = operation(number, 'plan')
    op = operation(number, 'execute')
    assert reviewed['operation'] == plan_op
    assert op['control_sha256'] == plan_op['control_sha256']
    plan = json.loads(Path(plan_op['local_result']).read_bytes())
    receipt = json.loads(Path(op['local_result']).read_bytes())
    assert receipt['applied'] == plan['rows']
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    for key in ('warm_files_written', 'source_or_project_object_files_changed', 'failed_evidence_archive_changed', 'compiler_invoked'):
        assert receipt[key] is False
    assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
    result = dict(scope=number, operation=op, rows=reviewed['rows'], disk_after_bytes=receipt['disk_after_bytes'], content_and_reversibility_preserved=True)
    path = ROOT/f'trace-cache-receipt-audit-v{number}.json'
    data = (json.dumps(result, indent=2)+'\n').encode()
    if path.exists(): assert path.read_bytes() == data
    else: path.open('xb').write(data)
    print(json.dumps(result))


if __name__ == '__main__':
    if sys.argv[1:] == ['plan']: plan_review()
    elif len(sys.argv) == 3 and sys.argv[1] == 'receipt': receipt_review(int(sys.argv[2]))
    else: raise SystemExit('Use plan or receipt NUMBER')
