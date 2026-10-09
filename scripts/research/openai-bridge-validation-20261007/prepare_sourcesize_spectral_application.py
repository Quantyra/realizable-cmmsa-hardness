"""Derive guarded actual material/dyadic consumers; no compiler or cloud operation."""
import hashlib
import json
from pathlib import Path
import re
import tarfile

HERE = Path(__file__).parent
PARENT = Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02')
ROOT = HERE / 'sourcesize-spectral-application-candidate-v2'
PREFIX = 'lean/PvNP/RealizableHardness/'
NS = 'PvNP.RealizableHardness.ActualSelectedComplementSourceSizeSpectralApplication'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    records = []
    statements = []
    opens = set()
    with tarfile.open(PARENT / 'input-archive.tar.gz') as archive:
        for module, name, dyadic in [
            ('ActualSelectedComplementSourceSizeOriginalApplication',
             'selected_actual_material_moment_bound_original', False),
            ('ActualSelectedComplementManuscriptDyadicMoment',
             'selected_actual_material_moment_bound_original_at_dyadic_exponent', True),
        ]:
            rel = PREFIX + module + '.lean'
            data = archive.extractfile(rel).read()
            assert sha(data) == manifest['project_sources'][rel]['sha256']
            text = data.decode('utf-8')
            opens.update(re.findall(r'(?m)^open PvNP\.[^\n]+', text))
            start = text.index('theorem ' + name + '\n')
            original = text[start:text.index(' := by', start)]
            premise = '\n    (hSpectral : Spectral47ExactContract sourceHeightCutoff)'
            assert original.count(premise) == 1
            renamed = name + '_spectral_discharged'
            transformed = original.replace('theorem ' + name, 'theorem ' + renamed, 1).replace(premise, '')
            # Reconstruct the complete original type, including every conclusion and guard.
            reconstructed = transformed.replace('theorem ' + renamed, 'theorem ' + name, 1).replace(
                '\n    (a : Real)', premise + '\n    (a : Real)', 1)
            assert reconstructed == original
            assert 'Instance N rows' in transformed and 'Instance N m' not in transformed
            proof = (' := by\n  exact PvNP.RealizableHardness.' + module + '.' + name +
                     ' I copies U A C T f\n    base sourceHeightCutoff hsel hA r hrd e he hfail\n'
                     '    ((PvNP.RealizableHardness.SourceSizeContractBridge.spectral47_contract_iff\n'
                     '      sourceHeightCutoff).mp\n'
                     '      (PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant sourceHeightCutoff))\n'
                     '    a ha' + (' hkDyadic hkm' if dyadic else '') + '\n')
            statements.append(transformed + proof)
            records.append(dict(source=rel, source_sha256=sha(data), theorem=name,
                                candidate_theorem=renamed, original_type_sha256=sha(original.encode()),
                                candidate_type_sha256=sha(transformed.encode()), exact_type_reconstruction=True))
    imports = ['ActualSelectedComplementSourceSizeOriginalApplication',
               'ActualSelectedComplementManuscriptDyadicMoment',
               'ActualFiniteAppendSpectral47ExactInhabitant', 'SourceSizeContractBridge']
    body = ('\n'.join('import PvNP.RealizableHardness.' + m for m in imports) +
            '\n\n/-! Uncompiled successor candidate: actual SourceSize material and caller-chosen\n'
            'dyadic consumers discharge Spectral47 through the native contract bridge.\n'
            'Original HC46 remains supplied by the original consumer. All other premises\n'
            'and conclusions are retained exactly. No source/runtime or manuscript GO. -/\n'
            'namespace ' + NS + '\n' + '\n'.join(sorted(opens)) +
            '\nopen PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment\n'
            'set_option autoImplicit false\nnoncomputable section\n'
            'attribute [local instance] Classical.propDecidable\n\n' +
            '\n'.join(statements) + '\ntheorem sourceSize_spectral47_inhabited (cutoff : Real → Nat) :\n'
            '    PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment.Spectral47ExactContract cutoff :=\n'
            '  (PvNP.RealizableHardness.SourceSizeContractBridge.spectral47_contract_iff cutoff).mp\n'
            '    (PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant cutoff)\n'
            '\nend\nend ' + NS + '\n').encode()
    checks = ('import ' + NS + '\n\n' + '\n'.join(
        '#check ' + NS + '.' + r['candidate_theorem'] + '\n#print axioms ' + NS + '.' + r['candidate_theorem']
        for r in records) + '\n\nexample (cutoff : Real → Nat) :\n'
        '    PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment.Spectral47ExactContract cutoff :=\n'
        '  (PvNP.RealizableHardness.SourceSizeContractBridge.spectral47_contract_iff cutoff).mp\n'
        '    (PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant cutoff)\n'
        '#print axioms ' + NS + '.sourceSize_spectral47_inhabited\n'
        '#print axioms PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant\n'
        '#print axioms PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact\n'
        '#print axioms PvNP.RealizableHardness.ActualSelectedComplementSourceSizeOriginalApplication.selected_actual_material_moment_bound_original\n'
        '#print axioms PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment.selected_actual_material_moment_bound_original_at_dyadic_exponent\n').encode()
    ROOT.mkdir(exist_ok=True)
    files = []
    for name, data in [('ActualSelectedComplementSourceSizeSpectralApplication.lean', body),
                       ('ActualSelectedComplementSourceSizeSpectralApplicationChecks.lean', checks)]:
        assert not data.startswith(b'\xef\xbb\xbf')
        stripped = re.sub(r'/\-.*?\-/|--[^\n]*', '', data.decode(), flags=re.S)
        assert not re.search(r'\b(?:sorry|admit|axiom)\b', stripped)
        assert not re.search(r'^\s*-[ \t]+', stripped, re.M)
        assert not re.search(r'[A-Za-z0-9_]\.\s+\w', stripped)
        path = ROOT / name
        if path.exists():
            assert path.read_bytes() == data
        else:
            path.write_bytes(data)
        files.append(dict(path=PREFIX + name, bytes=len(data), sha256=sha(data)))
    record = dict(schema='sourcesize-spectral-application-candidate-v2',
                  preserved_v1='sourcesize-spectral-application-candidate-v1',
                  repair='join four split qualified names; add named inhabitant and direct dependency axiom checks',
                  derivations=records, files=files, independent_rows_preserved=True,
                  only_type_change='rename and remove hSpectral; every other premise/conclusion unchanged',
                  frozen_full101_modified=False, native_verified=False, compiler_invoked=False,
                  cloud_operation=False, accepted=False, full_goal_complete=False)
    data = (json.dumps(record, indent=2) + '\n').encode()
    path = ROOT / 'derivation.json'
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.write_bytes(data)
    print(json.dumps(record))


if __name__ == '__main__':
    main()
