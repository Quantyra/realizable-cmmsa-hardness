"""Complete row/custody audit of qualified settled-cache recovery before trace."""
import json
import sys
from pathlib import Path
from custody_checks import digest,verify_local_custody
from full109_builder02_controller import ROOT
here=Path(__file__).parent
def main(action,number):
 assert action in ('plan','receipt') and number in range(84,90)
 scope=next(s for s in json.loads((here/'full109-trace-small-cache-control-derivation-v1.json').read_bytes())['scopes'] if s['number']==number)
 assert digest(here/scope['helper'])==scope['helper_sha256']
 assert digest(here/scope['controller'])==scope['controller_sha256']
 ops={}
 for path in (ROOT/'consumption-v3/cache-repoint-controls').glob('*/operation.json'):
  op=json.loads(path.read_bytes())
  if op['remote_control']==scope['remote_control'] and op['action'] in ('plan','execute'):
   assert op['action'] not in ops
   assert digest(op['local_result'])==op['result_sha256'] and op['control_sha256']==scope['helper_sha256']
   commands=json.loads((path.parent/'commands.json').read_bytes())
   assert commands and all(c['native_exit']==0 for c in commands)
   ops[op['action']]=op
 assert 'plan' in ops
 settled=ROOT.parent/scope['resource'];marker=json.loads((settled/'launch-once.json').read_bytes())
 check=Path(marker['preflight']);native=json.loads((check/'terminal-custody.json').read_bytes());stop=json.loads((check/'vm-termination.json').read_bytes())
 assert marker['run']==native['run']==stop['run']==scope['run']
 assert native['terminal']['native_terminal']
 assert stop['custody_verified_before_stop'] and stop['independent']['status']=='TERMINATED'
 assert str(stop['independent']['id'])=='7237681467779354904'
 custody=native['custody'];assert custody['remote_sha256']==scope['archive']
 verify_local_custody(custody['short_path'],custody['repository_path'],scope['archive'],custody['bytes'])
 assert digest(settled/'capture-manifest.json')==scope['manifest']
 # Cleanup requires settled custody/termination, not mathematical qualification of old failed attempts.
 plan=json.loads(Path(ops['plan']['local_result']).read_bytes())
 assert plan['old_root']=='/home/dfredriksen_quantyra_org/'+scope['run']+'/.lake/packages'
 assert plan['canonical_root']=='/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
 assert plan['original_archive_sha256']==scope['archive']
 assert not plan['executed'] and not plan['compiler_invoked'] and plan['hash_or_size_mismatches_skipped']==0
 prior=ROOT.parent/'full107-exact-product-energy-repair-resource02/consumption-v3/complete-trace-cache-plan-review-v1-v4-v8.json'
 assert digest(prior)=='14532AA9BF8EC20D6CF1B90934FDF481EB3B90B35AD8B310419F6C03E48A813D'
 baseline_record=next(r for r in json.loads(prior.read_bytes())['plans'] if r['scope']==4)['operation']
 assert digest(baseline_record['local_result'])==baseline_record['result_sha256']
 baseline=json.loads(Path(baseline_record['local_result']).read_bytes())
 index={r['relative']:r for r in baseline['rows']};assert len(index)==len(baseline['rows'])==19233
 assert len({r['relative'] for r in plan['rows']})==len(plan['rows'])
 assert len(plan['rows'])>0
 allocation_differences=[]
 for row in plan['rows']:
  assert row['relative'] in index
  prior_row=index[row['relative']]
  assert (row['bytes'],row['sha256'])==(prior_row['bytes'],prior_row['sha256'])
  assert row['bytes']>=1 and row['allocated_bytes']>0 and row['allocated_bytes']%512==0
  if row['allocated_bytes']!=prior_row['allocated_bytes']:
   allocation_differences.append(dict(relative=row['relative'],prior=prior_row['allocated_bytes'],current=row['allocated_bytes']))
 assert sum(r['allocated_bytes'] for r in plan['rows'])==plan['allocated_bytes']>=896*1024**2
 result=dict(scope=number,rows=len(plan['rows']),plan_sha256=ops['plan']['result_sha256'],
  prior_complete_review_sha256=digest(prior),all_actual_rows_match_prior_verified_byte_identities=True,physical_allocation_differences=allocation_differences,
  identity_level='Current byte equality, not exhaustive capture-time cache hashes',
  sources_and_project_objects_and_canonical_warm_files_excluded=True,compiler_invoked=False,trace_executed=False,accepted=False)
 if action=='receipt':
  receipt=json.loads(Path(ops['execute']['local_result']).read_bytes())
  assert receipt['applied']==plan['rows'] and receipt['content_identity_verified_after_repoint']
  assert receipt['reversible_by_copying_identical_canonical_bytes']
  for key in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'):assert receipt[key] is False
  assert receipt['disk_after_bytes']>receipt['disk_before_bytes']
  result.update(receipt_sha256=ops['execute']['result_sha256'],disk_after_bytes=receipt['disk_after_bytes'])
 target=ROOT/'consumption-v3'/f'cache-small-{action}-audit-native{number}-v1.json'
 data=(json.dumps(result,indent=2)+'\n').encode()
 if target.exists():assert target.read_bytes()==data
 else:target.open('xb').write(data)
 print(json.dumps(result))
if __name__=='__main__':main(sys.argv[1],int(sys.argv[2]))
