"""Check complete trace DAG structure and exact type-edge correspondence; no Lean."""
import collections
import hashlib
import json
from pathlib import Path
import sys


def natural(x):
    if type(x) is not int or x < 0:
        raise ValueError('Expected natural number')


def name(x):
    if x == []:
        return ''
    if not isinstance(x, list) or len(x) != 3 or x[0] not in ('str', 'num'):
        raise ValueError('Malformed Lean name')
    prefix = name(x[1])
    if x[0] == 'str':
        if not isinstance(x[2], str):
            raise ValueError('Malformed string name component')
    else:
        natural(x[2])
    return (prefix + '.' if prefix else '') + str(x[2])


def ref(x, limit):
    natural(x)
    if x >= limit:
        raise ValueError('Forward, cyclic or absent DAG reference')


def validate_dag(dag):
    if set(dag) != {'schema', 'root', 'expr_nodes', 'level_nodes'} or dag['schema'] != 'lean-expr-type-dag-v1':
        raise ValueError('Foreign DAG schema')
    levels, exprs = dag['level_nodes'], dag['expr_nodes']
    if not isinstance(levels, list) or not isinstance(exprs, list):
        raise ValueError('Malformed DAG arrays')
    for i, row in enumerate(levels):
        if not isinstance(row, list) or not row:
            raise ValueError('Malformed level')
        tag = row[0]
        arity = {'zero': 1, 'succ': 2, 'max': 3, 'imax': 3, 'param': 2, 'mvar': 2}
        if tag not in arity or len(row) != arity[tag]:
            raise ValueError('Unknown or malformed level')
        if tag in ('succ', 'max', 'imax'):
            for value in row[1:]:
                ref(value, i)
        elif tag in ('param', 'mvar'):
            name(row[1])
    constants = set()
    arity = {'bvar': 2, 'fvar': 2, 'mvar': 2, 'sort': 2, 'const': 3,
             'app': 3, 'lam': 5, 'forall': 5, 'let': 6, 'nat': 2,
             'string': 2, 'mdata': 3, 'proj': 4}
    children = []
    for i, row in enumerate(exprs):
        if not isinstance(row, list) or not row or row[0] not in arity or len(row) != arity[row[0]]:
            raise ValueError('Unknown or malformed expression')
        tag = row[0]
        refs = []
        if tag in ('bvar', 'nat'):
            natural(row[1])
        elif tag in ('fvar', 'mvar'):
            name(row[1])
        elif tag == 'sort':
            ref(row[1], len(levels))
        elif tag == 'const':
            constants.add(name(row[1]))
            if not isinstance(row[2], list):
                raise ValueError('Malformed constant levels')
            for value in row[2]:
                ref(value, len(levels))
        elif tag == 'app':
            refs = row[1:]
        elif tag in ('lam', 'forall'):
            name(row[1]); refs = row[2:4]
            if row[4] not in ('Lean.BinderInfo.default', 'Lean.BinderInfo.implicit', 'Lean.BinderInfo.strictImplicit', 'Lean.BinderInfo.instImplicit'):
                raise ValueError('Foreign binder information')
        elif tag == 'let':
            name(row[1]); refs = row[2:5]
            if type(row[5]) is not bool:
                raise ValueError('Malformed let flag')
        elif tag == 'string':
            if not isinstance(row[1], str):
                raise ValueError('Malformed literal')
        elif tag == 'mdata':
            refs = [row[1]]
            if not isinstance(row[2], str):
                raise ValueError('Malformed metadata annotation')
        elif tag == 'proj':
            name(row[1]); natural(row[2]); refs = [row[3]]
        for value in refs:
            ref(value, i)
        children.append(refs)
    ref(dag['root'], len(exprs))
    reached, pending = set(), [dag['root']]
    while pending:
        i = pending.pop()
        if i in reached:
            continue
        reached.add(i); pending.extend(children[i])
    if len(reached) != len(exprs):
        raise ValueError('Extraneous unreachable expression nodes')
    return constants


def main():
    source, target = map(Path, sys.argv[1:])
    raw = source.read_bytes()
    data = json.loads(raw)
    kinds = collections.Counter()
    hashes, modules, boundaries, structural_edges = {}, set(), {}, {}
    for key, row in data['nodes'].items():
        if row['name'] != key or row.get('unresolved'):
            raise ValueError('Missing or mismatched constant')
        constants = validate_dag(row['type_dag'])
        if constants != set(row['type_edges']):
            raise ValueError('Type DAG does not reproduce type edges: ' + key)
        body_type = set(row['type_edges']) | set(row['proof_edges'])
        union = set(row['union_edges'])
        if not body_type <= union:
            raise ValueError('Union edges omit a type/proof dependency: ' + key)
        extra = union - body_type
        # ConstantInfo includes inductive/constructor links beyond Expr constants.
        # Preserve those links and the native union graph; never discard them.
        if extra:
            if row['kind'] not in ('inductive', 'constructor'):
                raise ValueError('Unclassified structural dependency: ' + key)
            structural_edges[key] = sorted(extra)
        if row['body_unresolved'] or row['ownership_unresolved']:
            raise ValueError('Unresolved body or module: ' + key)
        kinds[(row['project'], row['kind'], row['body_available'])] += 1
        hashes[key] = hashlib.sha256(json.dumps(row['type_dag'], sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest().upper()
        if row['project']:
            modules.add(row['module'])
        else:
            boundaries[key] = {'module': row['module'], 'kind': row['kind'], 'body_available': row['body_available'], 'disposition': 'external kernel/library boundary; source review disposition pending'}
    for graph in data['graphs'].values():
        if graph['unresolved']:
            raise ValueError('Unresolved graph')
    result = {'schema': 'full89-type-dag-qualification-v1',
              'validated_graph_sha256': hashlib.sha256(raw).hexdigest().upper(),
              'nodes': len(hashes), 'exact_type_edge_matches': len(hashes),
              'project_modules': sorted(modules), 'type_dag_sha256': hashes,
              'external_boundaries': boundaries, 'additional_native_structural_edges': structural_edges,
              'kind_counts': [{'project': p, 'kind': k, 'body_available': b, 'count': count} for (p, k, b), count in sorted(kinds.items())],
              'structural_trace_qualification': True, 'boundary_dispositions_complete': False,
              'complete_review_coverage': False, 'reviewed': False, 'accepted': False}
    with target.open('x', encoding='utf-8') as output:
        json.dump(result, output, indent=2, ensure_ascii=False); output.write('\n')
    print(json.dumps({'nodes': len(hashes), 'project_modules': len(modules), 'external_boundaries': len(boundaries), 'structural_trace_qualification': True}))


if __name__ == '__main__':
    main()
