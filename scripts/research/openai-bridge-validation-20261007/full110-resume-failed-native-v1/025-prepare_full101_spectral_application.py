"""Prepare an exact original consumer application; static only, no Lean invocation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).parent
ROOT = HERE / 'full101-spectral-original-application-candidate-v1'
BASE = 'b27cdf79'
REL = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean'
CAPTURE = Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02/capture-manifest.json')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    source = subprocess.check_output(['git', 'show', BASE + ':' + REL])
    capture = json.loads(CAPTURE.read_bytes())
    assert sha(source) == capture['project_sources'][REL]['sha256']
    text = source.decode('utf-8')
    name = 'selected_leaf_high_energy_le_spectral'
    match = re.search(r'(?m)^theorem ' + name + r'\b', text)
    statement = text[match.start():text.index(' := by', match.start())]
    premise = '\n    (hSpectral : Spectral47ExactContract sourceHeightCutoff)'
    assert statement.count(premise) == 1
    newname = name + '_original_application'
    transformed = statement.replace('theorem ' + name, 'theorem ' + newname, 1).replace(premise, '')
    assert transformed.replace('theorem ' + newname, 'theorem ' + name, 1).replace(
        '\n    (hHeight : sourceHeightCutoff rho ≤ h)',
        '\n    (hHeight : sourceHeightCutoff rho ≤ h)' + premise, 1) == statement
    opens = '\n'.join(re.findall(r'(?m)^open PvNP\.[^\n]+', text))
    namespace = 'PvNP.RealizableHardness.ActualSelectedComplementSpectral47OriginalApplication'
    body = ('import PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant\n'
            'import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment\n\n'
            '/-! Original selected-leaf consumer with the Spectral47 oracle discharged.\n'
            'All source-height, rho, split and exact squared-energy guards are retained.\n'
            'This source is a candidate pending authoritative GCP kernel/axiom verification;\n'
            'it does not close exact manuscript eigenvalue/G-Phi or source/runtime gates. -/\n'
            'namespace ' + namespace + '\n\n' + opens + '\n'
            'open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment\n'
            'open PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant\n\n'
            'set_option autoImplicit false\nnoncomputable section\n'
            'attribute [local instance] Classical.propDecidable\n\n' + transformed + ' := by\n'
            '  exact selected_leaf_high_energy_le_spectral\n'
            '    (n := n) (c := c) (s := s) (h := h) (r := r) (rho := rho)\n'
            '    sourceHeightCutoff T f hEven hRho hc hs hHeight\n'
            '    (spectral47_exact_contract_inhabitant sourceHeightCutoff)\n\n'
            'end\nend ' + namespace + '\n').encode('utf-8')
    checks = ('import ' + namespace + '\n\n'
              '#check ' + namespace + '.' + newname + '\n'
              '#print axioms ' + namespace + '.' + newname + '\n').encode('utf-8')
    files = {'ActualSelectedComplementSpectral47OriginalApplication.lean': body,
             'ActualSelectedComplementSpectral47OriginalApplicationChecks.lean': checks}
    ROOT.mkdir(exist_ok=True)
    records = []
    for filename, data in files.items():
        decoded = data.decode('utf-8')
        assert not data.startswith(b'\xef\xbb\xbf') and not re.search(r'^\s*-[ \t]+', decoded, re.M)
        stripped = re.sub(r'/\-.*?\-/|--[^\n]*', '', decoded, flags=re.S)
        assert not re.search(r'\b(?:sorry|admit|axiom)\b', stripped)
        p = ROOT / filename
        if p.exists():
            assert p.read_bytes() == data
        else:
            with p.open('xb') as stream:
                stream.write(data)
        records.append(dict(path='lean/PvNP/RealizableHardness/' + filename, sha256=sha(data), bytes=len(data)))
    record = dict(schema='full101-original-spectral-consumer-candidate-v1', source_git_ref=BASE,
        original_consumer_path=REL, original_consumer_source_sha256=sha(source),
        original_statement_sha256=sha(statement.encode()), candidate_statement_sha256=sha(transformed.encode()),
        only_statement_change='Remove hSpectral caller premise and rename theorem; every other hypothesis and conclusion unchanged.',
        files=records, proof_calls_actual_original_consumer=True, proof_supplies_recovered_contract_inhabitant=True,
        full100_sources_profiles_and_stages_must_remain=True,
        exact_manuscript_eigenvalue_and_G_Phi_laws_remain_open=True,
        source_and_runtime_obligations_remain_open=True, native_verified=False, compiler_invoked=False,
        cloud_operation=False, accepted=False, full_goal_complete=False)
    data = (json.dumps(record, indent=2) + '\n').encode('utf-8')
    p = ROOT / 'derivation.json'
    if p.exists():
        assert p.read_bytes() == data
    else:
        with p.open('xb') as stream:
            stream.write(data)
    print(json.dumps(dict(files=records, derivation_sha256=sha(data), native_verified=False)))


if __name__ == '__main__':
    main()
