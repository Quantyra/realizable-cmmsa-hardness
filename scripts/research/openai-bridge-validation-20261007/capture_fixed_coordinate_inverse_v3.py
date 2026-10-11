"""Capture the reviewed fixed-coordinate candidate; no Lean or cloud execution."""
import hashlib
import json
from pathlib import Path
import re
import tarfile
import prepare_complete_numeric_scope_v2 as scope
from lean_source_static_preflight_v2 import inspect_bytes
from prepare_complete_operator_scope_v2 import declarations, imports

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    offer = HERE / 'numeric-fixed-coordinate-inverse-offer-v3'
    target = HERE / 'numeric-fixed-coordinate-inverse-capture-v3'
    manifest = json.loads((offer / 'manifest.json').read_bytes())
    assert {p.name for p in offer.iterdir()} == {'manifest.json'} | set(manifest['offered_files'])
    for name, row in manifest['offered_files'].items():
        data = (offer / name).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    assert sha((HERE / 'author_fixed_coordinate_inverse_v3.py').read_bytes()) == manifest['control_sha256']
    old = scope.parent()
    added, _, _ = scope.additions()
    all_sources = old | added
    for row in manifest['direct_project_dependencies']:
        data = all_sources[row['path']]
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    for folder, pin in manifest['numeric_captures']:
        assert sha((HERE / folder / 'index.json').read_bytes()) == pin
    source = (offer / 'ExactCoordinateNumericInverse.lean').read_bytes()
    assert sha(source) == 'BC0B039F43B5D62509118B698A8049A9AE5633A8DD2425C64F67293F206A3E3B'
    prior = HERE / 'numeric-fixed-coordinate-inverse-capture-v2'
    assert sha((prior / 'index.json').read_bytes()) == '036B77150529E49D00D6B6B32E576141B4E9613C3B013190BD8D7260A15F1B7F'
    before = (prior / 'ExactCoordinateNumericInverse.lean').read_bytes()
    assert before.count(b' /\\') == 3 and before.count(b'!= 0') == 1
    assert before.replace(b' /\\', ' ∧'.encode()).replace(b'!= 0', '≠ 0'.encode()) == source
    checks = (offer / 'ExactCoordinateNumericInverseChecks.lean').read_bytes()
    assert checks == (prior / 'ExactCoordinateNumericInverseChecks.lean').read_bytes()
    requests = re.findall(r'(?m)^#print axioms\s+(\S+)', checks.decode())
    assert requests == declarations(source) == manifest['public_declarations']
    assert len(requests) == 1
    body = source[source.index(b'theorem fixed_coordinate_real_inverse_agreement'):]
    assert all(token not in body for token in [b'I copies U', b'A.1', b'hcomp', b'hside', b'!=', b' /\\'])
    assert body.count(b'StarDensity (k := m)') == 1
    assert b'(k := m) hcenter hleaf CA TA' in body
    assert b'2 * selectedActualMoment' in body
    assert b'original_HC46_exact' in body and b'sourceSize_spectral47_inhabited cutoff' in body
    rank = old[manifest['copied_rankloss_source']['path']]
    assert sha(rank) == manifest['copied_rankloss_source']['sha256']
    for name in [b'selected_rankloss_exponent', b'rankloss_from_exponent']:
        start = rank.index(b'private theorem ' + name)
        next_doc = rank.find(b'\n/--', start)
        next_private = rank.find(b'\nprivate theorem ', start + 1)
        end = min(x for x in [next_doc, next_private] if x > start)
        assert rank[start:end].strip() in source
    package = scope.PARENT / 'checks/20261011T065940457444Z/qualified-native/cmmsa_a8_output_20261011T070000Z_135b1f28/remote-evidence/package-sources.tar.gz'
    assert sha(package.read_bytes()) == '494F97020D23F28340A2FC74049646C06BF07DF5E62EBA4FC4672C7704AB512D'
    with tarfile.open(package, 'r:gz') as tar:
        tactic = tar.extractfile('.lake/packages/mathlib/Mathlib/Tactic.lean').read()
        assert sha(tactic) == '434829FECFA75B2ADFE40364F2D58336BB25A469A83BB8214523657E746D43C9'
    lexical = [inspect_bytes(source, 'source'), inspect_bytes(checks, 'checks')]
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for p in sorted(offer.iterdir()):
        data = p.read_bytes()
        (target / p.name).open('xb').write(data)
        assert (target / p.name).read_bytes() == p.read_bytes() == data
        rows.append(dict(original=str(p), copy=p.name, bytes=len(data), sha256=sha(data)))
    report = dict(files=rows, lexical_preflight=lexical, requested_axioms=requests,
        parent_capture_index_sha256=sha((prior / 'index.json').read_bytes()),
        control_sha256=sha(Path(__file__).read_bytes()), actual_dependencies_reverified=True,
        exact_three_conjunction_one_not_equal_repair=True, checks_unchanged=True,
        root_read_entire_source_and_generic_material_API_binders=True,
        copied_private_arithmetic_exact=True, arbitrary_ordinary_tables_and_fixed_ambient=True,
        original_Real_threshold_and_outer_material_factor_two=True,
        static_review_concerns=[], compiler_invoked=False, accepted=False, full_goal_complete=False,
        remaining=['Native verification of this theorem and all dependencies',
                   'Transport one fixed coordinate frame to the actual complement',
                   'Robust refresh history, preservation probability, many-Q counting and cutoffs',
                   'Same-law decoder and actual source NO promise'])
    raw = (json.dumps(report, indent=2) + '\n').encode()
    (target / 'index.json').open('xb').write(raw)
    print(json.dumps(dict(capture=target.name, source_sha256=sha(source), index_sha256=sha(raw), compiler_invoked=False)))


if __name__ == '__main__':
    main()
