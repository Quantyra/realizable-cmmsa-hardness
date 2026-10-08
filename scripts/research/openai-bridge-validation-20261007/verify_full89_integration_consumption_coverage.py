"""Bound module coverage questions to the preserved native172/focused-four trace."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')


def main():
    graph_bytes = (BASE/'graphs/validated-graphs.json').read_bytes()
    index_bytes = (BASE/'review-sources/source-index.json').read_bytes()
    graph = json.loads(graph_bytes)
    index = json.loads(index_bytes)
    selected = {'PvNP.RealizableHardness.'+Path(r['path']).stem for r in index['project_bodies']}
    project = {name: node for name, node in graph['nodes'].items() if node['project']}
    modules = {node['module'] for node in project.values()}
    outside = sorted(modules-selected)
    if len(selected) != 170 or len(modules) != 158 or outside:
        raise ValueError('Native consumed module/body selection gap')
    absent = ['ActualBinaryMatrixHC46A9ActualFiber', 'ActualBinaryMatrixHC46CommonDerivative',
              'ActualBinaryMatrixHC46MixedPeeling', 'ActualBinaryMatrixHC46FinitePeeling']
    unused = {stem: sorted(name for name, n in project.items() if n['module'] == 'PvNP.RealizableHardness.'+stem)
              for stem in absent}
    if any(unused.values()):
        raise ValueError('Previously unreviewed imported module is actually consumed')
    enumerate_modules = ['ActualBinaryMatrixHC46A9InitialGraph', 'ActualBinaryMatrixHC46A7Transfer']
    reached = {stem: sorted(name for name, n in project.items() if n['module'] == 'PvNP.RealizableHardness.'+stem)
               for stem in enumerate_modules}
    receipt = {'schema': 'full89-integration-bounded-consumption-coverage-v1',
               'graph_sha256': hashlib.sha256(graph_bytes).hexdigest().upper(),
               'source_index_sha256': hashlib.sha256(index_bytes).hexdigest().upper(),
               'selected_complete_modules': len(selected), 'consumed_project_modules': len(modules),
               'project_modules_outside_selection': outside, 'unselected_import_module_reachable_constants': unused,
               'reached_constants_in_legacy_named_modules': reached,
               'scope': 'Only exact172-native and focused-four-consumer preserved graph union; not all repository uses or full material consumer closure.',
               'accepted': False}
    path = Path(__file__).with_name('full89-integration-consumption-coverage.json')
    with path.open('x', encoding='utf-8') as output:
        json.dump(receipt, output, indent=2); output.write('\n')
    print(json.dumps({'consumed_modules': len(modules), 'outside': outside,
                      'legacy_module_reached_counts': {k: len(v) for k, v in reached.items()}}))


if __name__ == '__main__':
    main()
