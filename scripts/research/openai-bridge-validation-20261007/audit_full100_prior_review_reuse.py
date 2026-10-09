"""Full325 source/context/type/proof identity reuse; no new semantic acceptance."""
import json
from pathlib import Path
from custody_checks import digest, verify_local_custody
from full100_consumption_v2_controller import ROOT

HERE = Path(__file__).parent
BASE = ROOT/'qualification'
OLD = ROOT.parent.parent/'full97-spectral-bridge-utf8-section-repair-resource02/consumption-v1/qualification'
OLD95 = ROOT.parent.parent/'full95-manuscript-moment-syntax-repair-resource02/consumption-v1/qualification'
OLD90 = ROOT.parent.parent/'full90-material-resource02/consumption-v1/qualification'

def read(path): return json.loads(Path(path).read_bytes())

def report(folder, lens, number=1):
    path = HERE/folder/(lens+'-'+str(number).zfill(2)+'.json')
    value = read(path)
    assert value['native_exit']==0 and value['actual_packet_context_fit']
    assert digest(path.with_suffix('.md'))==value['report_sha256']
    assert digest(value['raw_stdout_path'])==value['raw_stdout_sha256']
    for row in value['supplied_complete_files']:
        p = Path(row['source_root'])/row['path']
        assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes']
    return path,value

def main():
    old_index_path=OLD/'review-sources/source-index.json';new_index_path=BASE/'review-sources/source-index.json'
    old_index,new_index=read(old_index_path),read(new_index_path)
    old={r['path']:r for r in old_index['project_bodies']};new={r['path']:r for r in new_index['project_bodies']}
    assert (len(old),len(new))==(325,327)
    for path,row in old.items():
        target=new[path];assert (row['sha256'],row['bytes'])==(target['sha256'],target['bytes'])
        for folder in [OLD,BASE]:
            p=folder/'review-sources'/path;assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes']
    fresh=sorted(set(new)-set(old))
    assert fresh==['lean/PvNP/RealizableHardness/BinaryMatrixRightFourierCovariance.lean','lean/PvNP/RealizableHardness/BinaryMatrixRightOrbit.lean']
    graphs=[read(q/'graphs/validated-graphs.json') for q in [OLD,BASE]]
    dags=[read(q/'type-dag-qualification.json')['type_dag_sha256'] for q in [OLD,BASE]]
    assert (len(graphs[0]['nodes']),len(graphs[1]['nodes']))==(8072,8084)
    for name,row in graphs[0]['nodes'].items():
        target=graphs[1]['nodes'][name];assert dags[0][name]==dags[1][name]
        for field in ['kind','module','project','body_available','body_unresolved','ownership_unresolved']:assert row[field]==target[field]
        for field in ['type_edges','proof_edges','union_edges']:assert set(row[field])==set(target[field])
    manifests=[read(q.parent.parent/'capture-manifest.json') for q in [OLD,BASE]]
    for field in ['cache_provenance','configs']:assert manifests[0][field]==manifests[1][field]
    inherited=read(OLD/'prior-review-reuse-audit.json');prior95=read(OLD95/'prior-review-reuse-audit.json')
    assert inherited['reuse_identity_eligible'] and len(inherited['unchanged_prior_complete_bodies'])==323
    assert digest(old_index_path)==inherited['new_source_index_sha256']
    assert digest(OLD95/'review-sources/source-index.json')==inherited['old_source_index_sha256']
    assert digest(OLD/'graphs/validated-graphs.json')==inherited['new_graph_sha256']
    assert digest(OLD95/'graphs/validated-graphs.json')==inherited['old_graph_sha256']
    assert prior95['reuse_identity_eligible'] and len(prior95['unchanged_prior_complete_bodies'])==319
    assert digest(OLD95/'review-sources/source-index.json')==prior95['new_source_index_sha256']
    assert digest(OLD90/'review-sources/source-index.json')==prior95['old_source_index_sha256']
    assert digest(OLD95/'graphs/validated-graphs.json')==prior95['new_graph_sha256']
    assert digest(OLD90/'graphs/validated-graphs.json')==prior95['old_graph_sha256']
    assert len(prior95['prior_reports'])==18
    for row in prior95['prior_reports']:
        p,value=report('full90-material-'+row['kind']+'-reports',row['lens'],row['packet'])
        assert digest(p)==row['receipt_sha256'] and digest(p.with_suffix('.md'))==row['report_sha256']
    settlement=read(OLD95/'six-review-custody-v1/typed-custody-settlement.json');c=settlement['custody']
    verify_local_custody(c['short_path'],c['repository_path'],c['remote_sha256'],c['bytes'])
    assert settlement['native_exits_all_zero'] and settlement['actual_provider_context_fits_all_verified']
    old95_bodies={r['path']:r for r in read(OLD95/'review-sources/source-index.json')['project_bodies']}
    report_rows=[]
    for lens in ['proof-adversarial','complexity','non-claims']:
        coverage=set(prior95['unchanged_prior_complete_bodies'])
        for kind,folder in [('original','full95-material-integration-reports'),('addendum','full95-material-identity-addendum-reports')]:
            p,value=report(folder,lens)
            row=next(r for r in inherited['six_prior_Full95_reports'] if r['kind']==kind and r['lens']==lens)
            assert digest(p)==row['receipt_sha256'] and digest(p.with_suffix('.md'))==row['report_sha256']
            for source in value['supplied_complete_files']:
                if source['source_kind']=='project':
                    assert old95_bodies[source['path']]['sha256']==source['sha256'];coverage.add(source['path'])
        assert coverage==set(old95_bodies)
        coverage=set(inherited['unchanged_prior_complete_bodies'])
        p,value=report('full97-material-integration-reports',lens)
        for source in value['supplied_complete_files']:
            if source['source_kind']=='project':
                assert old[source['path']]['sha256']==source['sha256'];coverage.add(source['path'])
        assert coverage==set(old)
        report_rows.append(dict(lens=lens,receipt_sha256=digest(p),report_sha256=value['report_sha256'],all325_prior_body_coverage_identity_eligible=True))
    reconciliation=read(OLD/'material-review-root-reconciliation-v1.json')
    assert reconciliation['reports_read_in_full'] and reconciliation['all_three_new_body_soundness_checks_passed']
    assert not reconciliation['unconditional_material_or_manuscript_accepted']
    value=dict(schema='full100-prior-full325-review-reuse-identity-audit-v1',
        old_source_index_sha256=digest(old_index_path),new_source_index_sha256=digest(new_index_path),
        old_graph_sha256=digest(OLD/'graphs/validated-graphs.json'),new_graph_sha256=digest(BASE/'graphs/validated-graphs.json'),
        unchanged_prior_complete_bodies=list(old),new_or_changed_complete_bodies=fresh,changed_prior_bodies=[],
        shared_native_constant_types_and_edges_unchanged=8072,compiler_package_core_configuration_preserved=True,
        prior_Full97_reports=report_rows,prior_Full95_six_and_Full90_eighteen_reports_verified=True,
        prior_conditional_material_verdict=reconciliation['all_three_conditional_material_verdicts'],
        prior_remaining_high_scope=reconciliation['remaining_HIGH_scope'],
        full325_prior_semantic_coverage_identity_eligible=True,fresh_two_body_and_full_scope_integration_review_required=True,
        fresh_full327_rereading_claimed=False,actual_compiled_object_binary_custody_not_claimed=True,
        reuse_identity_eligible=True,accepted=False,full_goal_complete=False)
    path=BASE/'prior-review-reuse-audit.json'
    with path.open('x',encoding='utf-8') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    print(json.dumps(dict(prior_bodies=325,fresh_bodies=2,shared_nodes_unchanged=8072,prior_reports_verified=27,accepted=False)))

if __name__=='__main__':main()
