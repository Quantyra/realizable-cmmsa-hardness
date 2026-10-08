"""Connect actual native roots/consumer closures to complete immutable review bodies."""
import hashlib
import json
from pathlib import Path

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')


def main():
    graph_bytes = (ROOT/'graphs/validated-graphs.json').read_bytes()
    graphs = json.loads(graph_bytes)
    manifest_bytes = (ROOT/'review-packets/manifest.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    module_packets = {}
    for i, packet in enumerate(manifest['packets'], 1):
        data = Path(packet['path']).read_bytes()
        if hashlib.sha256(data).hexdigest().upper() != packet['sha256']:
            raise ValueError('Immutable packet changed')
        for row in packet['files']:
            module = row['path'].removeprefix('lean/').removesuffix('.lean').replace('/', '.')
            if module in module_packets:
                raise ValueError('Repeated complete source')
            module_packets[module] = {'packet': i, **row}
    roots = []
    for name in graphs['graphs']['exact172-native']['roots']:
        row = graphs['nodes'][name]
        if not row['project'] or row['module'] not in module_packets:
            raise ValueError('Native root lacks complete body selection')
        roots.append({'name': name, 'kind': row['kind'], 'module': row['module'],
                      'complete_source': module_packets[row['module']]})
    consumers = {}
    for root, reached in graphs['graphs']['focused-four-consumer']['per_root_reachability'].items():
        modules = {graphs['nodes'][n]['module'] for n in reached if graphs['nodes'][n]['project']}
        if not modules <= module_packets.keys():
            raise ValueError('Consumed module omitted from packets')
        consumers[root] = {'reachable_constants': len(reached),
                           'complete_project_sources': [module_packets[m] for m in sorted(modules)],
                           'required_packets': sorted({module_packets[m]['packet'] for m in modules}),
                           'external_boundary_count': sum(not graphs['nodes'][n]['project'] for n in reached)}
    result = {'schema': 'full89-native-root-review-coverage-map-v1',
              'graphs_sha256': hashlib.sha256(graph_bytes).hexdigest().upper(),
              'packet_manifest_sha256': hashlib.sha256(manifest_bytes).hexdigest().upper(),
              'native_roots': roots, 'native_root_count': len(roots),
              'focused_consumers': consumers, 'complete_source_count': len(module_packets),
              'selection_mapping_complete': True, 'all_required_review_verdicts_received': False,
              'cross_partition_integration_complete': False, 'accepted': False}
    with (ROOT/'review-packets/native-root-coverage-map.json').open('x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2); stream.write('\n')
    print(json.dumps({'native_roots': len(roots), 'focused_consumers': len(consumers), 'complete_sources': len(module_packets)}))


if __name__ == '__main__': main()
