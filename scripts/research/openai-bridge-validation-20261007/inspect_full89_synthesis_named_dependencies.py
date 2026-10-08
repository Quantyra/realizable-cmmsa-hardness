"""Enumerate exact trace membership requested by synthesis, without changing verdicts."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')


def main():
    raw = (BASE/'graphs/validated-graphs.json').read_bytes()
    graph = json.loads(raw)
    native_raw = (BASE/'integration-native-evidence-v1/native-review-evidence.json').read_bytes()
    native = json.loads(native_raw)
    targets = ['pseudorandom_atMost_of_exact', 'dr6_actual_complex_fourth_moment_over_162_le',
               'selected_actual_material_moment_bound', 'selected_actual_HC_spectral_moment_bound',
               'matching_center_mass_eq_grassmann_beta', 'selected_actual_source_dimension_bound',
               'nominal_score_mean_eq_raw_dim']
    results = []
    for target in targets:
        matches = [name for name in graph['nodes'] if name.split('.')[-1] == target]
        roots = {label: [root for root, reached in g['per_root_reachability'].items()
                         if any(name in reached or name == root for name in matches)]
                 for label, g in graph['graphs'].items()}
        fresh_roots = [root for root in roots['exact172-native'] if root in native['actual_profiles']]
        results.append({'declaration_suffix': target, 'exact_reached_names': matches,
                        'reaching_roots': roots, 'fresh_profiled_reaching_roots': fresh_roots,
                        'fresh172_transitive_axiom_coverage': bool(fresh_roots),
                        'absence_scope': 'Only the exact172 and focused-four trace; not all repository uses or historical profiles.'})
    if not all(row['fresh172_transitive_axiom_coverage'] for row in results[:2]):
        raise ValueError('Expected named dependency not reached by any fresh profiled root')
    receipt = {'schema': 'full89-synthesis-named-dependency-membership-v1',
               'graph_sha256': hashlib.sha256(raw).hexdigest().upper(),
               'native_evidence_sha256': hashlib.sha256(native_raw).hexdigest().upper(),
               'results': results, 'accepted': False}
    destination = Path(__file__).with_name('full89-synthesis-named-dependency-membership.json')
    with destination.open('x', encoding='utf-8') as output:
        json.dump(receipt, output, indent=2); output.write('\n')
    print(json.dumps([{'suffix': r['declaration_suffix'], 'reached': bool(r['exact_reached_names']),
                       'profiled_reaching_root_count': len(r['fresh_profiled_reaching_roots'])} for r in results]))


if __name__ == '__main__':
    main()
