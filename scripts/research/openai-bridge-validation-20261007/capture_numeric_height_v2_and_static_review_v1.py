"""Capture the repaired height offer and completed independent finite-max review."""
import hashlib
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from capture_numeric_offers_20261011_v1 import capture

HERE=Path(__file__).resolve().parent


def verify_members(group,key):
    archive=group[key];path=Path(archive['path']);assert digest(path)==archive['sha256'].upper()
    with tarfile.open(path,'r:gz') as tar:
        for name,row in group.items():
            if name==key:continue
            data=tar.extractfile(row['archive_member']).read()
            assert hashlib.sha256(data).hexdigest().upper()==row['sha256'].upper()
            if 'bytes' in row:assert len(data)==row['bytes']


def main():
    report=HERE/'numeric-no-v2-independent-static-review-v1/review.json'
    assert digest(report)=='BF34345F5C7198DFE3FF6DBA19215B1FD237EBABFE5FC6870920220E73BC4422'
    review=json.loads(report.read_bytes());inputs=review['reviewed_inputs'];root=Path(inputs['offer_directory'])
    for key,row in inputs.items():
        if key=='offer_directory':continue
        assert digest(root/row['path'])==row['sha256']
    verify_members(review['pinned_project_sources'],'Full110_input_archive')
    verify_members(review['pinned_mathlib_sources'],'Full110_package_sources_archive')
    offer=json.loads((HERE/'actual-numeric-explicit-height-candidate-v2/manifest.json').read_bytes())
    api=json.loads((HERE/'numeric-scalar-offer-capture-v6/OFFER-MANIFEST.json').read_bytes())['mathlib_api_source_v6']
    assert digest(Path(api['path']))==api['sha256'].upper()
    with tarfile.open(api['path'],'r:gz') as tar:
        for row in offer['pinned_mathlib_api_inspection']:
            data=tar.extractfile(row['member']).read()
            assert hashlib.sha256(data).hexdigest().upper()==row['sha256'].upper()
    parents=[(r['directory'],r['index_sha256'],r['source'],r['source_sha256']) for r in
             (offer['parent_source_height_capture'],offer['parent_scalar_capture'])]
    capture('actual-numeric-explicit-height-candidate-v2','numeric-explicit-height-offer-capture-v2','manifest.json',
        '062E162E1F7F0C4242850A73266209667D2208259F8A186D58F871689C517AF0',parents,
        ['Named proposition interfaces, explicit factor commutation and full max chain inspected.',
         'hlarge hmulN still uses exact mul_le_mul_of_nonneg_right whose left side is 1*N; explicitly simplify one_mul to obtain declared N.',
         'Map incorrectly says numericBase j <= numericHnum j; the used premise is r <= max(base j,Hnum j). Preserve and correct separately.',
         'Complete source translation remains uncompiled; other tactic/coercion defects may remain.'])
    target=HERE/'numeric-no-v2-static-review-capture-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (target/'review.json').open('xb').write(report.read_bytes());assert digest(target/'review.json')==digest(report)
    (target/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (target/'index.json').open('x').write(json.dumps(dict(original=str(report),files=[dict(path='review.json',
        bytes=report.stat().st_size,sha256=digest(report))],all_reported_source_archive_and_member_hashes_verified=True,
        complete_report_read=True,root_assessment='No findings are a static assessment, not an elaboration or kernel result.',
        compiler_invoked=False,native_verified=False,accepted=False),indent=2)+'\n')
    print(json.dumps(dict(review_capture=str(target),index_sha256=digest(target/'index.json'))),flush=True)


if __name__=='__main__':main()
