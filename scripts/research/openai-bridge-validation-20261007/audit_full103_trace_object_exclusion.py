"""Prove current-run cache recovery excludes the complete native object closure."""
import json
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from prepare_builder02_full103 import OUTPUT


def main():
    marker = json.loads((OUTPUT/'launch-once.json').read_bytes())
    receipt = json.loads((Path(marker['preflight'])/'terminal-custody.json').read_bytes())
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'],
                        custody['remote_sha256'], custody['bytes'])
    with tarfile.open(custody['repository_path']) as archive:
        objects = json.loads(archive.extractfile('object-after.json').read())
    assert len(objects) == 687
    reviewed = OUTPUT/'consumption-v2/trace-storage-plan-complete-review-v1-v2.json'
    first = json.loads(reviewed.read_bytes())['plans'][0]
    plan_path = Path(first['plan_path'])
    assert digest(plan_path) == first['plan_sha256']
    plan = json.loads(plan_path.read_bytes())
    assert plan['old_root'] == '/home/dfredriksen_quantyra_org/'+marker['run']+'/.lake/packages'
    repointed = {'.lake/packages/'+row['relative'] for row in plan['rows']}
    assert len(repointed) == 9672
    assert not set(objects) & repointed
    result = dict(schema='full103-trace-current-run-native-object-exclusion-v1',
        run=marker['run'], native_archive_sha256=custody['remote_sha256'],
        plan_sha256=first['plan_sha256'], plan_review_sha256=digest(reviewed),
        complete_native_objects=687, recovery_rows=9672, intersecting_objects=0,
        all_native_objects_excluded=True, compiler_invoked=False, accepted=False)
    path = Path(__file__).with_name('full103-trace-native-object-exclusion-v1.json')
    data = (json.dumps(result, indent=2)+'\n').encode()
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
