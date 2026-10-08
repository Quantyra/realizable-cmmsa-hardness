"""Derive an explicit same-material-consumer export without changing Full89."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')
SOURCE = BASE/'review-sources'
DESTINATION = BASE/'material-consumer-candidate-v1'
MATERIAL = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMoment.lean'
APPLICATION = 'lean/PvNP/RealizableHardness/ActualSelectedComplementHC46OriginalApplication.lean'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    index_bytes = (SOURCE/'source-index.json').read_bytes()
    rows = {r['path']: r for r in json.loads(index_bytes)['project_bodies']}
    material = (SOURCE/MATERIAL).read_bytes()
    application = (SOURCE/APPLICATION).read_bytes()
    for path, data in [(MATERIAL, material), (APPLICATION, application)]:
        if sha(data) != rows[path]['sha256'] or len(data) != rows[path]['bytes']:
            raise ValueError('Pinned consumer source changed')
    text = material.decode('utf-8')
    start = text.index('theorem selected_actual_material_moment_bound\n')
    finish = text.index(' := by\n', start)
    original_statement = text[start:finish]
    premise = '    (hHC : HC46ExactContract)\n'
    if original_statement.count(premise) != 1:
        raise ValueError('Unexpected material premise')
    statement = original_statement.replace('theorem selected_actual_material_moment_bound\n',
                                          'theorem selected_actual_material_moment_bound_original\n', 1)
    statement = statement.replace(premise, '', 1)
    if statement.replace('selected_actual_material_moment_bound_original', 'selected_actual_material_moment_bound', 1) != original_statement.replace(premise, '', 1):
        raise ValueError('Material statement drift')
    prelude = text.split('set_option autoImplicit false', 1)[0]
    opens = '\n'.join(line for line in prelude.splitlines() if line.startswith('open '))
    addition = '\n/-! Same material consumer with only the universal HC46 premise discharged.\nSpectral47, selector, failed-zoom and positive-parameter premises remain explicit.\nThis candidate has not been compiled or independently accepted. -/\n'
    addition += opens+'\nattribute [local instance] Classical.propDecidable\n\n'+statement+' := by\n'
    addition += ('  exact selected_actual_material_moment_bound I copies U A C T f\n'
                 '    base sourceHeightCutoff hsel hA r hrd e he hfail\n'
                 '    original_HC46_exact hSpectral a ha\n\n')
    closing = 'end\nend PvNP.RealizableHardness.ActualSelectedComplementHC46OriginalApplication\n'
    before = application.decode('utf-8')
    if not before.endswith(closing) or before.count(closing) != 1:
        raise ValueError('Unexpected original application namespace boundary')
    candidate = (before[:-len(closing)]+addition+closing).encode('utf-8')
    DESTINATION.mkdir()
    (DESTINATION/'ActualSelectedComplementHC46OriginalApplication.lean').write_bytes(candidate)
    receipt = {'schema': 'full89-same-material-consumer-candidate-v1',
               'parent_application_path': APPLICATION, 'parent_application_sha256': sha(application),
               'material_path': MATERIAL, 'material_sha256': sha(material),
               'source_index_sha256': sha(index_bytes), 'candidate_sha256': sha(candidate),
               'candidate_bytes': len(candidate), 'original_material_statement_sha256': sha(original_statement.encode()),
               'candidate_statement_sha256': sha(statement.encode()),
               'exact_statement_change': 'Rename declaration and remove only hHC : HC46ExactContract; identical explicit conclusion and other premises.',
               'proof_argument': 'original_HC46_exact passed to original same-material theorem; same I/copies/U/A/C/T/f and coordinate bridge.',
               'frozen_capture_modified': False, 'local_compilation': False,
               'native_verification_pending': True, 'support_body_coverage_pending': True,
               'fresh_axiom_profile_pending': True, 'consumption_trace_pending': True,
               'launch_clearance': False, 'accepted': False,
               'remaining_contract': 'Spectral47ExactContract sourceHeightCutoff',
               'numeric_NO_and_full_manuscript_gates_open': True}
    (DESTINATION/'derivation.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    technical = Path(__file__).parent
    with (technical/'full89-material-consumer-candidate.lean').open('xb') as output:
        output.write(candidate)
    with (technical/'full89-material-consumer-candidate.json').open('x', encoding='utf-8') as output:
        output.write(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'candidate_sha256': sha(candidate), 'bytes': len(candidate), 'accepted': False, 'launch_clearance': False}))


if __name__ == '__main__':
    main()
