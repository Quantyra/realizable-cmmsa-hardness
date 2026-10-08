"""Index recorded native reachability, without inferring body or claim acceptance."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification')


def main():
    path = BASE/'graphs/validated-graphs.json'
    data = path.read_bytes()
    graph = json.loads(data)
    nodes = graph['nodes']
    parents = {name: [] for name in nodes}
    for name, node in nodes.items():
        for edge in node['union_edges']:
            if edge in parents:
                parents[edge].append(name)
    reach = graph['graphs']['exact173-native']['per_root_reachability']
    focused = graph['graphs']['focused-five-consumer']['per_root_reachability']
    roots_by_node = {name: [] for name in nodes}
    for root, reached in reach.items():
        for name in reached:
            if name in roots_by_node:
                roots_by_node[name].append(root)
    modules = {}
    for name, node in nodes.items():
        module = node['module'] or ''
        if not (node['project'] or module.startswith('Complexitylib.')):
            continue
        modules.setdefault(module, []).append(dict(name=name, kind=node['kind'],
            native_roots=sorted(roots_by_node[name]),
            focused_roots=[root for root, reached in focused.items() if name in reached],
            direct_project_parents=sorted(p for p in parents[name] if nodes[p]['project'])))
    output = dict(schema='full90-recorded-per-constant-reachability-v1',
        graph_sha256=hashlib.sha256(data).hexdigest().upper(),
        native_roots=len(reach), focused_roots=len(focused), modules=modules,
        scope='Recorded union of type and proof reach only; namespace does not replace declaring module.',
        body_review_accepted=False, mathematical_acceptance=False)
    target = BASE/'reached-constant-index-v1.json'
    with target.open('x', encoding='utf-8') as f:
        json.dump(output, f, indent=2); f.write('\n')
    print(json.dumps(dict(path=str(target), modules=len(modules),
                         complexitylib={m:[r['name'] for r in rows] for m,rows in modules.items() if m.startswith('Complexitylib.')})))


if __name__ == '__main__':
    main()
