"""Verify complete Full103 source/type/proof/review identity reuse; grant no new acceptance."""
import json
from pathlib import Path
from custody_checks import digest
from audit_full100_prior_review_reuse import report
from full105_consumption_v3_controller import ROOT
HERE=Path(__file__).parent
BASE=ROOT/'qualification'
PARENT=ROOT.parent.parent/'full103-spectral-owned-warning-repair-resource02/consumption-v2/qualification-v3'
LENSES=['proof-adversarial','complexity','non-claims']
def read(path):return json.loads(Path(path).read_bytes())
def main():
 old_index,new_index=[read(p/'review-sources/source-index.json') for p in [PARENT,BASE]]
 old,new=[{r['path']:r for r in index['project_bodies']} for index in [old_index,new_index]]
 assert (len(old),len(new))==(340,344)
 for rel,row in old.items():
  assert (row['sha256'],row['bytes'])==(new[rel]['sha256'],new[rel]['bytes'])
  for root in [PARENT,BASE]:
   p=root/'review-sources'/rel;assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes']
 fresh=sorted(set(new)-set(old));assert len(fresh)==4
 graphs=[read(p/'graphs/validated-graphs.json') for p in [PARENT,BASE]]
 dags=[read(p/'type-dag-qualification.json')['type_dag_sha256'] for p in [PARENT,BASE]]
 assert (len(graphs[0]['nodes']),len(graphs[1]['nodes']))==(8260,8269)
 for name,row in graphs[0]['nodes'].items():
  target=graphs[1]['nodes'][name];assert dags[0][name]==dags[1][name]
  for field in ['kind','module','project','body_available','body_unresolved','ownership_unresolved']:assert row[field]==target[field]
  for field in ['type_edges','proof_edges','union_edges']:assert set(row[field])==set(target[field])
 manifests=[read(p.parent.parent/'capture-manifest.json') for p in [PARENT,BASE]]
 for field in ['cache_provenance','configs']:assert manifests[0][field]==manifests[1][field]
 prior_path=PARENT/'prior-review-reuse-audit.json';prior=read(prior_path)
 assert digest(prior_path)=='1F3EFC11692E14A6D44CBF2971C1E626265E8F79DCF7C35C6A0170A507589C68'
 assert prior['all327_per_lens_prior_body_coverage_identity_eligible'] and len(prior['reports'])==33
 assert digest(PARENT/'review-sources/source-index.json')==prior['new_source_index_sha256']
 assert digest(PARENT/'graphs/validated-graphs.json')==prior['new_graph_sha256']
 settlement_path=HERE/'full103-material-integration-reports/root-reconciliation-v1.json';settlement=read(settlement_path)
 assert digest(settlement_path)=='1F60172EEA3C5399E6F86E582F9379CABD02908C539647489BDF8505BE5F294C'
 assert settlement['reports_read_in_full'] and settlement['all_three_fresh_spectral_body_soundness_checks_passed']
 reports=[]
 def retain(folder,lens,number,expected):
  p,value=report(folder,lens,number)
  assert digest(p)==expected['receipt_sha256'] and value['report_sha256']==expected['report_sha256'] and value['raw_stdout_sha256']==expected['raw_stdout_sha256']
  raw=read(value['raw_stdout_path']);assert not raw.get('is_error',False) and raw['num_turns']==value['num_turns']==1 and value.get('subagents_spawned',0)==0
  reports.append(dict(path=str(p),folder=folder,lens=lens,packet=number,receipt_sha256=digest(p),report_sha256=value['report_sha256'],raw_stdout_sha256=value['raw_stdout_sha256'],native_exit=0,actual_context_fit=True));return value
 for row in prior['reports']:
  number=int(Path(row['path']).stem.rsplit('-',1)[1]);retain(row['folder'],row['lens'],number,row)
 for lens in LENSES:
  expected=next(r for r in settlement['reports'] if r['lens']==lens)
  assert expected['fresh13_files_all_declarations_inspected'] and expected['required_fresh_bodies_skipped']==0 and expected['actual_context_fit']
  value=retain('full103-material-integration-reports',lens,1,expected)
  covered=set(prior['unchanged_prior_complete_bodies'])
  for row in value['supplied_complete_files']:
   if row['source_kind']=='project':assert row['sha256']==old[row['path']]['sha256'];covered.add(row['path'])
  assert covered==set(old)
 assert len(reports)==36
 result=dict(schema='full105-full340-prior-review-identity-reuse-v1',old_source_index_sha256=digest(PARENT/'review-sources/source-index.json'),new_source_index_sha256=digest(BASE/'review-sources/source-index.json'),old_graph_sha256=digest(PARENT/'graphs/validated-graphs.json'),new_graph_sha256=digest(BASE/'graphs/validated-graphs.json'),prior_reuse_audit_sha256=digest(prior_path),prior_root_settlement_sha256=digest(settlement_path),unchanged_prior_complete_bodies=list(old),fresh_complete_bodies=fresh,shared_native_type_and_body_dependency_context_unchanged=8260,compiler_package_core_cache_configuration_preserved=True,reports=reports,all340_per_lens_prior_body_coverage_identity_eligible=True,fresh4_body_and_full_integration_review_required=True,prior_scope_findings_and_HIGH_residues_retained=True,current344_fresh_rereading_claimed=False,accepted=False,full_goal_complete=False)
 data=(json.dumps(result,indent=2)+'\n').encode();out=BASE/'prior-review-reuse-audit.json'
 if out.exists():assert out.read_bytes()==data
 else:out.open('xb').write(data)
 (HERE/'full105-prior-review-reuse-audit-v1.json').write_bytes(data)
 print(json.dumps(dict(prior_bodies=340,fresh_bodies=4,shared_nodes=8260,actual_prior_reports_verified=36,audit_sha256=digest(out),accepted=False)))
if __name__=='__main__':main()
