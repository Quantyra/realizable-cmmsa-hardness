"""Freeze the root-repaired complete source candidate with actual dependency identities."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes
from prepare_complete_operator_scope_v2 import declarations, imports
from prepare_complete_numeric_scope_v2 import parent, additions, CAPTURES, PARENT, INPUT_SHA, MANIFEST_SHA

HERE = Path(__file__).resolve().parent
OFFER = HERE / 'numeric-same-instance-composition-offer-v2'
STEM = 'ExactNumericSameInstanceComposition'
PUBLIC = 'PvNP.RealizableHardness.' + STEM + '.same_instance_real_inverse_agreement'


def sha(raw):
    return hashlib.sha256(raw).hexdigest().upper()


def main():
    old = parent()
    added, _, provenance = additions()
    sources = dict(old, **added)
    source = (OFFER / (STEM + '.lean')).read_bytes()
    checks = (OFFER / (STEM + 'Checks.lean')).read_bytes()
    assert declarations(source) == [PUBLIC]
    assert re.findall(r'(?m)^#print axioms\s+(\S+)', checks.decode()) == [PUBLIC]
    lexical = [inspect_bytes(raw, name) for raw, name in
               [(source, STEM + '.lean'), (checks, STEM + 'Checks.lean')]]
    original_path = HERE / 'numeric-same-instance-interrupted-draft-record-v1/index.json'
    interrupted = json.loads(original_path.read_bytes())
    rows = [r for r in interrupted['files'] if r['original'].endswith(STEM + '.lean')]
    assert rows and all(r['sha256'] == '8E25E80159DCFBC31491C7D4BD0862C4B48CA1D632040DE5EE2C7F553F69F613' for r in rows)
    before = (original_path.parent / rows[0]['copy']).read_bytes()
    assert sha(before) == rows[0]['sha256']

    def header(raw):
        text = raw.decode('utf-8')
        start = text.index('theorem same_instance_real_inverse_agreement')
        return text[start:text.index(' := by\n', start)]

    expected = header(before)
    header_changes = [
        ('ActualMaximalPairLadder.CoordAmbient', 'ActualComplementCoordinateMassBridge.CoordAmbient'),
        ('ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateLeafTable',
         'ActualComplementCoordinateMassBridge.selectedCoordinateLeafTable'),
        ('        (ActualStarFixedRhoDimensionGuard.leafK m\n'
         '          (ActualCmmsaParameterReconciliation.hBlock L m)) C T : Real)) :',
         '        m C T : Real)) :')]
    for prior, after in header_changes:
        assert prior in expected
        expected = expected.replace(prior, after)
    assert header(source) == expected, 'Unreviewed public assumption or conclusion change'
    assert '(k := m)' in source.decode() and '(k := s)' not in source.decode()
    assert 'let epsRat : Rat := ActualStarAcceptedGoodMass.successMargin E' in source.decode()
    assert 'let etaRat : Rat := ActualNumericNo.actualAgreementMaximum (r := r) Tc' in source.decode()
    dependency_rows = []
    for module in imports(source):
        if module.startswith('PvNP.'):
            name = 'lean/' + module.replace('.', '/') + '.lean'
            raw = sources[name]
            dependency_rows.append(dict(module=module, path=name, bytes=len(raw), sha256=sha(raw),
                                        origin='frozen numeric candidate' if name in added else 'Full114 input'))
    definitions = set()
    for path, raw in sources.items():
        if not path.endswith('.lean'):
            continue
        text = raw.decode('utf-8')
        namespaces = re.findall(r'(?m)^namespace ([\w.]+)', text)
        if not namespaces:
            continue
        for match in re.finditer(r'(?m)^(?:(?:private|noncomputable|protected) )*'
                                 r'(?:def|abbrev|theorem|lemma|structure|inductive|class) (\w+)', text):
            definitions.add(namespaces[0] + '.' + match[1])
    references = sorted(set(re.findall(r'\b(Actual\w+\.\w+)\b', source.decode())))
    assert all('PvNP.RealizableHardness.' + ref in definitions for ref in references)
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    packages = Path(marker['preflight']) / 'qualified-native' / marker['run'] / 'remote-evidence/package-sources.tar.gz'
    package_pin = '494F97020D23F28340A2FC74049646C06BF07DF5E62EBA4FC4672C7704AB512D'
    assert digest(packages) == package_pin
    parent_manifest = json.loads(old['capture-manifest.json'])
    external = []
    with tarfile.open(packages, 'r:gz') as archive:
        for module in imports(source):
            if not module.startswith('PvNP.'):
                assert module.startswith('Mathlib.')
                member = '.lake/packages/mathlib/' + module.replace('.', '/') + '.lean'
                raw = archive.extractfile(member).read()
                assert sha(raw) == parent_manifest['cache_provenance']['package_sources'][member]
                external.append(dict(module=module, member=member, bytes=len(raw), sha256=sha(raw)))
    offered = {}
    assert {p.name for p in OFFER.iterdir()} == {STEM + '.lean', STEM + 'Checks.lean', 'ARGUMENT-AND-API-MAP.md'}
    for path in sorted(OFFER.iterdir()):
        offered[path.name] = dict(bytes=path.stat().st_size, sha256=digest(path))
    manifest = dict(offer=OFFER.name, status='Complete source candidate; uncompiled and unaccepted',
                    parent_input_sha256=INPUT_SHA, parent_manifest_sha256=MANIFEST_SHA,
                    interrupted_draft_index_sha256=digest(original_path), public_declarations=[PUBLIC],
                    direct_project_dependencies=dependency_rows, numeric_capture_indices=CAPTURES,
                    candidate_source_provenance=provenance, package_sources_sha256=package_pin,
                    external_dependencies=external, offered_files=offered, lexical_preflight=lexical,
                    exact_public_header_corrections=header_changes,
                    canonical_project_reference_names_verified=references,
                    density_threshold_and_maximum_agreement_are_distinct=True,
                    star_count_is_m_append_width_is_leafK_source_rows_independent=True,
                    original_Real_threshold_and_same_instance_tables_preserved=True,
                    no_external_signal_material_or_contract_premise_added=True,
                    compiler_invoked=False, accepted=False, full_research_complete=False)
    (OFFER / 'manifest.json').open('x').write(json.dumps(manifest, indent=2) + '\n')
    capture = HERE / 'numeric-same-instance-composition-capture-v2'
    capture.mkdir(exist_ok=False)
    (capture / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    files = []
    for path in sorted(OFFER.iterdir()):
        raw = path.read_bytes()
        (capture / path.name).open('xb').write(raw)
        assert (capture / path.name).read_bytes() == raw
        files.append(dict(original=str(path), copy=path.name, bytes=len(raw), sha256=sha(raw)))
    result = dict(files=files, public_declarations=[PUBLIC], lexical_preflight=lexical,
                  root_reviewed_complete_argument_and_actual_source_interfaces=True,
                  exact_diff=''.join(difflib.unified_diff(before.decode().splitlines(True), source.decode().splitlines(True))),
                  public_header_corrections=header_changes, actual_project_and_candidate_imports_verified=True,
                  canonical_name_check_is_not_Lean_elaboration=True, compiler_invoked=False, accepted=False,
                  control_sha256=digest(__file__))
    (capture / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(dict(capture=capture.name, index_sha256=digest(capture / 'index.json'),
                         source_sha256=sha(source), public_requests=1, compiled=False)), flush=True)


if __name__ == '__main__':
    main()
