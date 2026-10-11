"""Capture the repaired same-witness physical consequence without compiling."""
import hashlib
import json
from pathlib import Path
import re
import tarfile
import prepare_complete_numeric_scope_v2 as scope
from lean_source_static_preflight_v2 import inspect_bytes
from prepare_complete_operator_scope_v2 import declarations

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    offer = HERE / 'numeric-physical-density-offer-v4'
    prior = HERE / 'numeric-physical-density-capture-v3'
    assert sha((prior / 'index.json').read_bytes()) == '0E583EB62D091F532968E2B4E3C4D42FB1A927851FE0564A56FF5B39A91B52D2'
    raw = (offer / 'manifest.json').read_bytes()
    assert sha(raw) == '7B6FDCE92C2890E2CC240D172489FB13029BBBBF98496BDE584EC4C96CE4B79E'
    m = json.loads(raw)
    assert {p.name for p in offer.iterdir()} == {'manifest.json'} | {r['file'] for r in m['offered_files']}
    for row in m['offered_files']:
        data = (offer / row['file']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    old = scope.parent()
    for row in m['project_dependencies']:
        data = old[row['member']]
        assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
    for row in m['captured_numeric_dependencies']:
        folder = HERE / row['capture']
        assert sha((folder / 'index.json').read_bytes()) == row['capture_index_sha256']
        assert sha((folder / (row['module'] + '.lean')).read_bytes()) == row['source_sha256']
        for r in json.loads((folder / 'index.json').read_bytes())['files']:
            data = (folder / r.get('copy', r.get('path'))).read_bytes()
            assert len(data) == r['bytes'] and sha(data) == r['sha256']
    with tarfile.open(scope.PARENT / 'input-archive.tar.gz', 'r:gz') as tar:
        for row in [m['input']['lake_manifest'], m['input']['lean_toolchain']]:
            data = tar.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256'].upper()
    source = (offer / 'ActualNumericPhysicalDensity.lean').read_bytes()
    before = (prior / 'ActualNumericPhysicalDensity.lean').read_bytes()
    assert sha(source) == '58BBC9F6D120FFC7435DDA5437821C9CE14B573F275187B6D14D302E3201DDE2'
    # Retain all earlier declarations and the new declaration's entire statement.
    marker = b'theorem selected_physical_density_with_rows'
    a, b = [x.index(b' := by\n', x.index(marker)) for x in [before, source]]
    assert before[:a] == source[:b]
    expected = before.replace(b'taggedAccepts I copies Tsel', b'taggedAccepts I copies C Tsel')
    expected = expected.replace(b'orderedStarLaw I copies (t :=', b'orderedStarLaw I copies J (t :=')
    start_old = expected.index(b'  have hhigh := high_density_mass')
    start_new = source.index(b'  let mu := uniformLaw')
    stop_old = expected.index(b'  have hrows :', start_old)
    stop_new = source.index(b'  have hrows :', start_new)
    expected = expected[:start_old] + source[start_new:stop_new] + expected[stop_old:]
    a = b'    intro P\n    rw [taggedSelectedDomainTable_apply'
    b = b'    intro P\n    change P.respectsRows I copies\n      ((taggedSelectedDomainTable I copies raw s) (P.domain I copies))\n    rw [taggedSelectedDomainTable_apply'
    assert expected.count(a) == 1
    expected = expected.replace(a, b)
    assert expected == source
    assert b'high_density_mass' not in source
    checks = (offer / 'ActualNumericPhysicalDensityChecks.lean').read_bytes()
    assert checks == (prior / 'ActualNumericPhysicalDensityChecks.lean').read_bytes()
    requests = re.findall(r'(?m)^#print axioms\s+(\S+)', checks.decode())
    assert requests == m['requested_axioms'] == declarations(source) and len(requests) == 3
    lexical = [inspect_bytes(source, 'source'), inspect_bytes(checks, 'checks')]
    target = HERE / 'numeric-physical-density-capture-v4'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for p in sorted(offer.iterdir()):
        data = p.read_bytes()
        (target / p.name).open('xb').write(data)
        assert (target / p.name).read_bytes() == p.read_bytes() == data
        rows.append(dict(original=str(p), copy=p.name, bytes=len(data), sha256=sha(data)))
    report = dict(files=rows, parent_capture_index_sha256=sha((prior / 'index.json').read_bytes()),
        actual_project_numeric_and_toolchain_dependencies_reverified=True,
        lexical_preflight=lexical, requested_axioms=requests,
        root_read_entire_added_theorem_and_repair_diff_and_actual_API_signatures=True,
        public_statements_checks_old_declarations_unchanged=True,
        explicit_center_and_block_arguments_fixed=True, finite_average_proved_inline=True,
        same_selected_witness_row_validity_and_uniform_mass=True,
        metadata_errata=['Author could not locate lean_source_static_preflight_v2.py; root found and executed the exact local script. Its result is lexical only, not Lean grammar or elaboration.'],
        static_review_concerns=[], compiler_invoked=False, accepted=False,
        control_sha256=sha(Path(__file__).read_bytes()))
    raw = (json.dumps(report, indent=2) + '\n').encode()
    (target / 'index.json').open('xb').write(raw)
    print(json.dumps(dict(capture=target.name, source_sha256=sha(source), index_sha256=sha(raw), compiler_invoked=False)))


if __name__ == '__main__':
    main()
