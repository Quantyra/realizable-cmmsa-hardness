"""Preserve the fixed-frame assessment and both explicitly scoped text originals."""
import hashlib
import json
from pathlib import Path
import prepare_complete_numeric_scope_v2 as scope

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    offer = HERE / 'numeric-fixed-frame-transport-assessment-v1'
    raw = (offer / 'manifest.json').read_bytes()
    assert sha(raw) == '2C78278935E1EAD73113D96EC7AADB13A29C66FAA5B4F6E3BF35F36E96886D91'
    m = json.loads(raw)
    assert {p.name for p in offer.iterdir()} == {'ASSESSMENT.md', 'manifest.json'}
    assessment = (offer / 'ASSESSMENT.md').read_bytes()
    assert len(assessment) == m['files']['ASSESSMENT.md']['bytes']
    assert sha(assessment) == m['files']['ASSESSMENT.md']['sha256']
    old = scope.parent()
    for row in list(m['project_sources'].values()) + m['additional_context_sources']:
        data = old[row['member']]
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    c = m['fixed_coordinate_inverse']
    folder = HERE / c['capture']
    assert sha((folder / 'index.json').read_bytes()) == c['capture_index_sha256']
    assert sha((folder / (c['module'] + '.lean')).read_bytes()) == c['source_sha256']
    originals = [(offer / 'ASSESSMENT.md', 'ASSESSMENT.md'), (offer / 'manifest.json', 'manifest.json')]
    for key in ['canonical_manuscript', 'noncanonical_observation']:
        row = m[key]
        path = Path(row['path'])
        assert sha(path.read_bytes()) == row['sha256']
        originals.append((path, key + '.md'))
    target = HERE / 'numeric-fixed-frame-transport-assessment-capture-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for path, name in originals:
        data = path.read_bytes()
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == path.read_bytes() == data
        rows.append(dict(original=str(path), copy=name, bytes=len(data), sha256=sha(data)))
    result = dict(files=rows, actual_project_dependencies_verified=8,
        fixed_coordinate_candidate_and_index_verified=True,
        canonical_manuscript_authority_unchanged=True,
        noncanonical_text_preserved_only_as_scoped_observation=True,
        root_read_report_manifest_and_relevant_actual_API_signatures=True,
        material_finding='Matching-functional event equivalence is not full table acceptance; direct naturality, decoded-pair agreement and H-extension remain.',
        compiler_invoked=False, accepted=False, control_sha256=sha(Path(__file__).read_bytes()))
    data = (json.dumps(result, indent=2) + '\n').encode()
    (target / 'index.json').open('xb').write(data)
    print(json.dumps(dict(capture=target.name, index_sha256=sha(data), originals=len(rows), compiler_invoked=False)))


if __name__ == '__main__':
    main()
