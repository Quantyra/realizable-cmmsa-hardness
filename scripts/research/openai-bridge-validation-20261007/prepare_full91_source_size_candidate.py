"""Author additive, uncompiled source-row-independent material modules.

The frozen Full90 bodies remain unchanged. Only source equation cardinality
is generalized; the selected arity, analytic RHS and retained guards stay.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification/review-sources')
DEST = Path(__file__).parent / 'full91-source-size-candidate-v1'
PREFIX = 'lean/PvNP/RealizableHardness/'
RENAMES = {
    'ActualSelectedComplementAppendMoment': 'ActualSelectedComplementSourceSizeAppendMoment',
    'ActualSelectedComplementAnalyticMoment': 'ActualSelectedComplementSourceSizeAnalyticMoment',
    'ActualSelectedComplementHC46OriginalApplication': 'ActualSelectedComplementSourceSizeOriginalApplication',
}


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    index_data = (ROOT / 'source-index.json').read_bytes()
    pins = {r['path']: r for r in json.loads(index_data)['project_bodies']}
    artifacts = []
    expected_counts = [2, 2, 1]
    candidates = []
    for (old, new), expected in zip(RENAMES.items(), expected_counts):
        rel = PREFIX + old + '.lean'
        data = (ROOT / rel).read_bytes()
        assert sha(data) == pins[rel]['sha256'] and len(data) == pins[rel]['bytes'], rel
        text = data.decode('utf-8')
        binder = '{N m L samplerA : Nat}'
        assert text.count(binder) == expected, rel
        text = text.replace(binder, '{N rows m L samplerA : Nat}')
        instance = 'Instance N m)'
        assert text.count(instance) == expected, rel
        text = text.replace(instance, 'Instance N rows)')
        for before, after in RENAMES.items():
            text = text.replace(before, after)
        if old == 'ActualSelectedComplementHC46OriginalApplication':
            # The original analytic inhabitant still imports the old namespace;
            # explicitly import the generalized analytic consumer as well.
            text = 'import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment\n' + text
        candidate = text.encode('utf-8')
        # Exact inverse parity guards all other mathematical tokens and proofs.
        inverse = text
        if old == 'ActualSelectedComplementHC46OriginalApplication':
            inverse = inverse.removeprefix('import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment\n')
        for before, after in RENAMES.items():
            inverse = inverse.replace(after, before)
        inverse = inverse.replace('{N rows m L samplerA : Nat}', binder)
        inverse = inverse.replace('Instance N rows)', instance)
        assert inverse.encode('utf-8') == data, rel
        assert 'Instance N m)' not in text
        artifacts.append({'parent_path': rel, 'parent_sha256': sha(data),
                          'candidate_path': PREFIX + new + '.lean',
                          'candidate_sha256': sha(candidate), 'bytes': len(candidate),
                          'generalized_binders': expected, 'inverse_exact_byte_parity': True})
        candidates.append((new + '.lean', candidate))
    DEST.mkdir()
    for name, data in candidates:
        (DEST / name).write_bytes(data)
    receipt = {'schema': 'full91-source-size-candidate-v1',
               'source_index_sha256': sha(index_data), 'artifacts': artifacts,
               'source_rows_independent_of_selected_arity': True,
               'original_full90_sources_modified': False,
               'selected_parameter_and_same_instance_tables_preserved': True,
               'original_conditional_scope_preserved_as_rows_equals_m_specialization': True,
               'local_compilation': False, 'native_verification_pending': True,
               'fresh_profiles_and_consumption_and_review_pending': True,
               'joint_premise_inhabitance_proven': False,
               'Spectral47_numeric_NO_source_star_runtime_gates_open': True,
               'launch_clearance': False, 'accepted': False}
    (DEST / 'derivation.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
