"""Negative controls use labeled derived fixtures; retained archives are untouched."""
import hashlib,json,sys
from pathlib import Path
from unittest.mock import patch
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
import full118_authorized39_custody_v2 as a
import full118_pending39_custody_v1 as p
import custody_checks

def main():
 d=H/'full118-authorized39-custody-tests-v2';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 guard=a.configured_guard();approved,receipt=guard.documents();checks=[]
 new=[r for r in approved.values() if r['kind']=='short_complete_native_duplicate'];assert len(new)==3
 for row in new:
  result=guard.reconcile(row['remove'],row['retain_complete_native_archive'],row['sha256'],row['bytes'])
  assert result['current_retained_copies_verified']==1 and result['new_two_copy_custody'] is False
 checks.append(dict(test='all_three_new_archives_honest_one_copy',passed=True))
 for name in ['PLAN14','PLAN18']:
  module=sys.modules['full115_cumulative_cleanup_custody_v2'];plan=json.loads(getattr(module,name).read_bytes());row=plan['files'][0]
  result=guard.reconcile(row['remove'],row['retain_original'],row['sha256'],row['bytes']);assert result['current_retained_copies_verified']==1
 checks.append(dict(test='approved14_and18_cumulative_truth_preserved',passed=True))
 def reject(name,fn):
  try:fn()
  except (ValueError,OSError,KeyError) as e:checks.append(dict(test=name,rejected=True,reason=str(e)))
  else:raise AssertionError(name)
 reject('missing_receipt',lambda:p.ActualReceipt(d/'absent.json',a.RECEIPT_PIN,a.AUTH))
 raw=a.RECEIPT.read_bytes();mut=d/'changed-receipt-bytes.json';mut.write_bytes(raw+b'\n')
 reject('changed_receipt_bytes_same_fields',lambda:p.ActualReceipt(mut,a.RECEIPT_PIN,a.AUTH))
 def fixture(name,edit,authorization=a.AUTH):
  folder=d/name;folder.mkdir();j=json.loads(raw);edit(j);q=folder/'receipt.json';q.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
  (folder/'authorization.json').write_bytes((a.RECEIPT.parent/'authorization.json').read_bytes());(folder/'approved-plan.json').write_bytes(p.PLAN.read_bytes())
  pin=hashlib.sha256(q.read_bytes()).hexdigest().upper();return a.Authorized39Custody(p.ActualReceipt(q,pin,authorization))
 reject('unapproved_receipt',lambda:fixture('unapproved',lambda j:j.update(authorization_received=False)).documents())
 reject('wrong_authorization',lambda:fixture('wrong-authorization',lambda j:None,'not the actual authorization').documents())
 reject('mismatched_removed_path',lambda:fixture('wrong-path',lambda j:j['files'][0].update(removed=str(d/'unapproved-target.tar.gz'))).documents())
 reject('wrong_plan_pin',lambda:fixture('wrong-plan',lambda j:j.update(approved_plan_sha256='0'*64)).documents())
 f=fixture('changed-auth-bytes',lambda j:None);q=f.actual.path.parent/'authorization.json';q.write_bytes(q.read_bytes()+b'\n')
 reject('changed_complete_authorization_bytes',lambda:f.documents())
 row=new[-1]
 reject('mismatched_retained_path',lambda:guard.reconcile(row['remove'],new[0]['retain_complete_native_archive'],row['sha256'],row['bytes']))
 original=custody_checks.digest
 def changed(path):return '0'*64 if Path(path).resolve()==Path(row['retain_complete_native_archive']).resolve() else original(path)
 with patch.object(custody_checks,'digest',side_effect=changed):
  reject('changed_retained_archive_bytes_simulated_hash_only',lambda:guard.reconcile(row['remove'],row['retain_complete_native_archive'],row['sha256'],row['bytes']))
 result=dict(checks=checks,actual_receipt_sha256=a.RECEIPT_PIN,authorization_sha256=a.AUTH_PIN,retained_archives_modified=False,fixture_documents_are_deliberately_invalid_derivatives=True,production_adapter_activated=False,cloud_operation=False,lean_executed=False)
 (d/'result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(tests=len(checks),all_passed=True)))
if __name__=='__main__':main()
