"""Preserve two static-rejected originals before any successor repair. No Lean."""
import hashlib
import json
from pathlib import Path
import re
import tarfile
import prepare_complete_numeric_scope_v2 as scope
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def capture(offer, target, report):
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for p in sorted(offer.iterdir()):
        data = p.read_bytes()
        (target / p.name).open('xb').write(data)
        assert (target / p.name).read_bytes() == p.read_bytes() == data
        rows.append(dict(original=str(p), copy=p.name, bytes=len(data), sha256=sha(data)))
    report.update(files=rows, compiler_invoked=False, accepted=False,
                  repair_required=True, capture_control_sha256=sha(Path(__file__).read_bytes()))
    data = (json.dumps(report, indent=2) + '\n').encode()
    (target / 'index.json').open('xb').write(data)
    print(json.dumps(dict(capture=target.name, index_sha256=sha(data), rejected_static=True)))


def main():
    old = scope.parent()
    added, _, _ = scope.additions()
    all_sources = old | added
    offer = HERE / 'numeric-physical-density-offer-v3'
    manifest_raw = (offer / 'manifest.json').read_bytes()
    assert sha(manifest_raw) == '13AB780DB2312973D935FA798C43A2FB8C2E03AA966EE9DFF74A6A314EA7FE0D'
    m = json.loads(manifest_raw)
    assert {p.name for p in offer.iterdir()} == {'manifest.json'} | {r['file'] for r in m['offered_files']}
    for row in m['offered_files']:
        data = (offer / row['file']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    for row in m['project_dependencies']:
        data = old[row['member']]
        assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
    for row in m['captured_numeric_dependencies']:
        folder = HERE / row['capture']
        assert sha((folder / 'index.json').read_bytes()) == row['capture_index_sha256']
        assert sha((folder / (row['module'] + '.lean')).read_bytes()) == row['source_sha256']
    with tarfile.open(scope.PARENT / 'input-archive.tar.gz', 'r:gz') as tar:
        for row in [m['input']['lake_manifest'], m['input']['lean_toolchain']]:
            data = tar.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
    prior = HERE / 'numeric-physical-density-capture-v2'
    assert sha((prior / 'index.json').read_bytes()) == m['parent_offer']['capture_index_sha256']
    source = (offer / 'ActualNumericPhysicalDensity.lean').read_bytes()
    before = (prior / 'ActualNumericPhysicalDensity.lean').read_bytes()
    restored = source[:source.index(b'/-- A fixed selected instance and fixed global tables with a high unconditioned\nphysical score yield the selected representative choice')].rstrip() + b'\n\nend\nend PvNP.RealizableHardness.ActualNumericPhysicalDensity'
    for directive in ['import', 'open']:
        for name in ['ActualTaggedOrderedClassCollisionBound', 'ActualTaggedOrderedFullLawForce', 'ActualTaggedSelectedDecoderBridge']:
            part = (directive + ' PvNP.RealizableHardness.' + name + '\n').encode()
            assert restored.count(part) == 1
            restored = restored.replace(part, b'')
    assert restored == before
    checks = (offer / 'ActualNumericPhysicalDensityChecks.lean').read_bytes()
    assert checks.startswith((prior / 'ActualNumericPhysicalDensityChecks.lean').read_bytes())
    assert source.count(b'taggedAccepts I copies Tsel') == 2
    assert source.count(b'orderedStarLaw I copies (t :=') == 1
    assert source.count(b'have hhigh := high_density_mass') == 1
    assert b'private theorem high_density_mass' in old[scope.PREFIX + 'ActualTaggedFixedUDensityForce.lean']
    capture(offer, HERE / 'numeric-physical-density-capture-v3', dict(
        actual_dependencies_reverified=True, v2_source_exact_inverse_preservation=True,
        v2_checks_exact_prefix_preserved=True, parent_capture_sha256=sha((prior / 'index.json').read_bytes()),
        lexical_preflight=[inspect_bytes(source, 'source'), inspect_bytes(checks, 'checks')],
        static_review_concerns=[
            'Two taggedAccepts calls omit explicit center table C.',
            'One orderedStarLaw call omits explicit J.',
            'high_density_mass is private in another module; prove finite average locally.',
            'Map presents the private helper as an available API; correct this boundary.'],
        root_read_new_theorem_map_manifest_and_exact_preservation_diff=True,
        statement_boundary='Same selected witness, row validity and full eligible-U mass; no new premise.'))
    offer = HERE / 'numeric-fixed-coordinate-inverse-offer-v1'
    m = json.loads((offer / 'manifest.json').read_bytes())
    assert {p.name for p in offer.iterdir()} == {'manifest.json'} | set(m['offered_files'])
    for name, row in m['offered_files'].items():
        data = (offer / name).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    for row in m['direct_project_dependencies']:
        data = all_sources[row['path']]
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    source = (offer / 'ExactCoordinateNumericInverse.lean').read_bytes()
    assert sha(source) == 'A6E0E1AF249983A15558E5E2C86DE836A952999BB2B578C14CE3EDF3C887F0F6'
    assert b'numericRankThreshold m /        Fintype.card' in source
    control = HERE / 'author_fixed_coordinate_inverse_v1.py'
    assert sha(control.read_bytes()) == m['control_sha256']
    capture(offer, HERE / 'numeric-fixed-coordinate-inverse-capture-v1', dict(
        actual_dependencies_reverified=True, original_author_control_sha256=sha(control.read_bytes()),
        lexical_preflight=inspect_bytes(source, 'source'),
        static_review_concerns=['Python non-raw statement string consumed two backslash-newline conjunctions; emitted Lean statement is malformed.',
            'The author control emitted SyntaxWarning: invalid escape sequence in material string.',
            'Lexical preflight passed but checks neither Lean grammar nor elaboration.'],
        original_author_execution=dict(chunk_id='7887b7', exit_code=0,
            warning='SyntaxWarning: invalid escape sequence', complete_stream_retained_in_tool_history=True),
        repair='Use raw statement/material strings in a disjoint v2 control and offer; preserve every original.'))


if __name__ == '__main__':
    main()
