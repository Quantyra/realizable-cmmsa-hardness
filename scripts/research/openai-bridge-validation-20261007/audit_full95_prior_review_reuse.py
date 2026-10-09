"""Verify exact prior body/native identities without inventing new review acceptance."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02')


def main():
    old_base = BASE/'full90-material-resource02/consumption-v1/qualification'
    new_base = BASE/'full95-manuscript-moment-syntax-repair-resource02/consumption-v1/qualification'
    old_index_bytes = (old_base/'review-sources/source-index.json').read_bytes()
    new_index_bytes = (new_base/'review-sources/source-index.json').read_bytes()
    old_index = json.loads(old_index_bytes); new_index = json.loads(new_index_bytes)
    old = {r['path']: r for r in old_index['project_bodies']}
    new = {r['path']: r for r in new_index['project_bodies']}
    eligible = [path for path in old if path in new and old[path]['sha256'] == new[path]['sha256'] and old[path]['bytes'] == new[path]['bytes']]
    changed = [path for path in old if path not in eligible]
    if len(old) != 319 or len(new) != 323 or len(eligible) != 319 or changed:
        raise ValueError('Unexpected complete-body reuse scope')
    old_graph_bytes = (old_base/'graphs/validated-graphs.json').read_bytes()
    new_graph_bytes = (new_base/'graphs/validated-graphs.json').read_bytes()
    old_graph = json.loads(old_graph_bytes); new_graph = json.loads(new_graph_bytes)
    old_dag = json.loads((old_base/'type-dag-qualification.json').read_bytes())['type_dag_sha256']
    new_dag = json.loads((new_base/'type-dag-qualification.json').read_bytes())['type_dag_sha256']
    for name, row in old_graph['nodes'].items():
        target = new_graph['nodes'].get(name)
        if target is None or old_dag[name] != new_dag[name]: raise ValueError('Prior constant/type changed: '+name)
        for field in ['kind','module','project','body_available','body_unresolved','ownership_unresolved']:
            if row[field] != target[field]: raise ValueError('Prior constant identity changed: '+name)
        for field in ['type_edges','proof_edges','union_edges']:
            if set(row[field]) != set(target[field]): raise ValueError('Prior dependency edges changed: '+name)
    parent_manifest = json.loads((BASE/'full90-material-resource02/capture-manifest.json').read_bytes())
    current_manifest = json.loads((BASE/'full95-manuscript-moment-syntax-repair-resource02/capture-manifest.json').read_bytes())
    if parent_manifest['cache_provenance'] != current_manifest['cache_provenance'] or parent_manifest['configs'] != current_manifest['configs']:
        raise ValueError('Compiler/package/core/configuration context changed')
    coverage=json.loads((old_base/'material-review-coverage-snapshot-v2.json').read_bytes())
    inherited=json.loads((old_base/'prior-review-reuse-audit.json').read_bytes())
    if not coverage['all_packet_terminals_present'] or not inherited['reuse_identity_eligible']:
        raise ValueError('Prior complete reviewed body coverage absent')
    reports=[]
    coverage_by_lens={lens:set(inherited['unchanged_prior_complete_bodies']) for lens in ['proof-adversarial','complexity','non-claims']}
    for row in inherited['prior_reports']:
        folder=BASE/'full89-resource02/consumption-v2/qualification/review-packets'/f"{row['lens']}-{row['packet']:02d}"
        raw=(folder/'stdout.json').read_bytes()
        if hashlib.sha256(raw).hexdigest().upper()!=row['raw_stdout_sha256'] or int((folder/'native-exit.txt').read_text())!=0:
            raise ValueError('Inherited raw provider evidence changed')
    for lens in ['proof-adversarial','complexity','non-claims']:
        for kind,count in [('review',5),('integration',1)]:
            folder=Path(__file__).parent/('full90-material-'+kind+'-reports')
            for number in range(1,count+1):
                key=f'{lens}-{number:02d}'
                raw=(folder/(key+'.json')).read_bytes();r=json.loads(raw)
                body=(folder/(key+'.md')).read_bytes()
                if r['native_exit'] != 0 or hashlib.sha256(body).hexdigest().upper()!=r['report_sha256']:
                    raise ValueError('Prior complete report absent or changed')
                if hashlib.sha256(Path(r['raw_stdout_path']).read_bytes()).hexdigest().upper()!=r['raw_stdout_sha256']:
                    raise ValueError('Prior raw provider evidence changed')
                if not r['actual_packet_context_fit']:
                    raise ValueError('Prior actual context fit unproven')
                for source in r['supplied_complete_files']:
                    data=(Path(source['source_root'])/source['path']).read_bytes()
                    if len(data)!=source['bytes'] or hashlib.sha256(data).hexdigest().upper()!=source['sha256']:
                        raise ValueError('Prior complete supplied source changed')
                    if source['source_kind']=='project':
                        if source['path'] not in old or old[source['path']]['sha256']!=source['sha256']:
                            raise ValueError('Prior body does not match sealed old source index')
                        coverage_by_lens[lens].add(source['path'])
                reports.append({'lens':lens,'kind':kind,'packet':number,'receipt_sha256':hashlib.sha256(raw).hexdigest().upper(),'report_sha256':r['report_sha256']})
    if any(paths != set(old) for paths in coverage_by_lens.values()):
        raise ValueError('Full319 prior per-lens complete body coverage unproven')
    result = {'schema':'full95-prior-review-reuse-identity-audit-v1',
              'old_source_index_sha256':hashlib.sha256(old_index_bytes).hexdigest().upper(),
              'new_source_index_sha256':hashlib.sha256(new_index_bytes).hexdigest().upper(),
              'old_graph_sha256':hashlib.sha256(old_graph_bytes).hexdigest().upper(),
              'new_graph_sha256':hashlib.sha256(new_graph_bytes).hexdigest().upper(),
              'unchanged_prior_complete_bodies':eligible,'changed_prior_bodies':changed,
              'new_or_changed_complete_bodies':[path for path in new if path not in eligible],
              'shared_native_constant_types_and_edges_unchanged':len(old_graph['nodes']),
              'compiler_package_core_configuration_preserved':True,'prior_reports':reports,
              'reuse_identity_eligible':True,'material_scope_integration_and_critical_reread_required':True,
              'new_review_complete':False,'accepted':False,'full_goal_complete':False}
    path = new_base/'prior-review-reuse-audit.json'
    with path.open('x',encoding='utf-8') as output:
        json.dump(result,output,indent=2); output.write('\n')
    print(json.dumps({'eligible_prior_bodies':len(eligible),'new_or_changed_bodies':len(result['new_or_changed_complete_bodies']),
                      'shared_nodes_unchanged':len(old_graph['nodes']),'prior_reports':len(reports)}))


if __name__ == '__main__':
    main()
