"""Bounded actual-consumption disposition for packet4 legacy A7 charge notes."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')


def main():
    raw = (BASE/'graphs/validated-graphs.json').read_bytes()
    qualification = json.loads((BASE/'type-dag-qualification.json').read_bytes())
    if hashlib.sha256(raw).hexdigest().upper() != qualification['validated_graph_sha256']:
        raise ValueError('Changed qualified graph')
    graph = json.loads(raw)
    roots = graph['graphs']['exact172-native']['roots']
    focused = graph['graphs']['focused-four-consumer']['per_root_reachability']
    if len(roots) != 172 or len(focused) != 4 or any(g['unresolved'] for g in graph['graphs'].values()):
        raise ValueError('Trace scope incomplete')
    prefix = 'PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer.'
    legacy = [prefix+n for n in ['a7_a9_preceding_output_sum_le',
              'a7_a9_preceding_output_graph_charge', 'a7_a9_zero_parent_family_le']]
    selected = ['PvNP.RealizableHardness.ActualBinaryMatrixHC46A11WeightedAggregate.'+n
                for n in ['a11_weighted_actual_mixed_le_final_sum', 'manuscript_A7_actual']]
    legacy_rows = {n: {'requested_native_root': n in roots, 'present_in_complete172_trace': n in graph['nodes'],
                      'focused_consumers': [r for r, seen in focused.items() if n in seen]} for n in legacy}
    selected_rows = {n: {'requested_native_root': n in roots,
                        'focused_consumers': [r for r, seen in focused.items() if n in seen]} for n in selected}
    if any(r['present_in_complete172_trace'] for r in legacy_rows.values()):
        raise ValueError('Legacy dependency is actually consumed; investigate')
    if not all(len(r['focused_consumers']) == 4 for r in selected_rows.values()):
        raise ValueError('Intended A11 route missing')
    path = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A11WeightedAggregate.lean'
    data = (BASE/'review-sources'/path).read_bytes()
    index = json.loads((BASE/'review-sources/source-index.json').read_bytes())
    pin = next(r for r in index['project_bodies'] if r['path'] == path)
    if hashlib.sha256(data).hexdigest().upper() != pin['sha256']:
        raise ValueError('Changed A11 source')
    result = {'schema': 'full89-legacy-a7-consumption-disposition-v1',
              'validated_graph_sha256': qualification['validated_graph_sha256'],
              'scope': 'Actual dependency trace of exact172 native roots and four focused consumers only; not an all-repository or all-manuscript absence claim.',
              'legacy': legacy_rows, 'selected_a11_route': selected_rows,
              'a11_complete_source_pin': pin,
              'source_inspection': 'At lines1207-1260, a11_original_weighted_mixed_bound supplies hS through aggregate/fiber/tail bounds; manuscript_A7_actual constructs the strict lower-degree IH by simultaneous strong induction.',
              'independent_integration_confirmation_pending': True, 'accepted': False}
    with Path(__file__).with_name('full89-legacy-a7-consumption-disposition.json').open('x', encoding='utf-8') as output:
        json.dump(result, output, indent=2); output.write('\n')
    print(json.dumps({'flagged_legacy_nodes_reached': 0, 'focused_consumers_reaching_selected_a11_route': 4}))


if __name__ == '__main__': main()
