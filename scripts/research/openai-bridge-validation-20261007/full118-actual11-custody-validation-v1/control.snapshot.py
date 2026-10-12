"""Actual receipt mutation and bounded retained-byte negative checks, no evidence edits."""
import sys,json,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
import full118_authorized11_custody_v2 as a
import execute_full118_approved11_cleanup_v1 as e
from custody_checks import digest
from dataclasses import replace

def main():
 d=H/'full118-actual11-custody-validation-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');tests=[]
 def reject(name,f):
  try:f()
  except (ValueError,AssertionError,FileNotFoundError):tests.append({'case':name,'rejected':True})
  else:raise AssertionError(name)
 guard=a.configured_guard();approved,_=guard.documents();tests.append({'case':'complete_actual11_receipt','passed':True})
 for p,r in approved.items():
  if 'archive_terminal_member_sha256' in r:
   got=guard.reconcile(p,r['retained_archive'],r['remove_sha256'],r['remove_bytes']);assert got['current_retained_copies_verified']==1 and got['new_two_copy_custody'] is False
 tests.append({'case':'all_eight_consumption_custodies_honest_one_copy','passed':True})
 p=H/'full115-native-terminal-custody-v1/complete-originals.tar.gz';assert guard.retired_portable_payload(p)['exact_original_members']==110;tests.append({'case':'all110_retired_terminal_members_retained','passed':True})
 actual=guard.actual
 receipt=d/'receipt-mutant.NOT-ACTUAL.json';receipt.write_bytes(a.RECEIPT.read_bytes()+b'\n');reject('changed_receipt_bytes_same_required_strings',lambda:replace(actual,path=receipt))
 auth=d/'auth-mutant.NOT-APPROVAL.json';auth.write_bytes(a.AUTH.read_bytes()+b'\n');reject('changed_authorization_bytes_same_required_strings',lambda:replace(actual,authorization_path=auth))
 reject('missing_actual_receipt',lambda:replace(actual,path=d/'absent.json'))
 reject('wrong_whole_receipt_pin',lambda:replace(actual,sha256='0'*64))
 reject('wrong_user_authorization_text',lambda:a.prior.Pending11Custody(replace(actual,user_reply='NOT THE ACTUAL USER AUTHORIZATION')).documents())
 reject('wrong_reply_identity',lambda:a.prior.Pending11Custody(replace(actual,source_reply_id='NOT THE ACTUAL REPLY')).documents())
 r=next(r for r in approved.values() if 'archive_terminal_member_sha256' in r);p=Path(r['remove']);reject('wrong_current_retained_path',lambda:guard.reconcile(p,d/'wrong-retained.tar.gz',r['remove_sha256'],r['remove_bytes']));reject('wrong_remote_archive_pin',lambda:guard.reconcile(p,r['retained_archive'],'0'*64,r['remove_bytes']))
 fixture=d/'changed-retained-bytes.NOT-EVIDENCE';fixture.write_bytes(b'actual changed retained byte fixture\n');row=dict(r,retained_archive=str(fixture),retained_archive_bytes=fixture.stat().st_size)
 reject('retained_byte_hash_mismatch_bounded_fixture',lambda:e.identities(row,False))
 reject('missing_user_reply',lambda:e.authorization({'approved':True,'explicit_user_authorization':True,'approved_plan_sha256':e.PIN,'source_reply_id':'test'}))
 reject('unapproved_scope',lambda:e.authorization({'approved':False,'explicit_user_authorization':True,'approved_plan_sha256':e.PIN,'source_reply_id':'test','user_reply':'NOT APPROVAL'}))
 assert a.prior.custody_checks.verify_local_custody is a.prior.ORIGINAL
 j={'checks':tests,'all_passed':True,'actual_receipt_sha256':a.RECEIPT_PIN,'actual_authorization_sha256':a.AUTH_PIN,'pending_adapter_sha256':a.PENDING_PIN,'actual_adapter_sha256':digest(Path(a.__file__)),'evidence_mutated':False,'production_adapter_installed':False,'retained_byte_test_is_explicit_small_fixture_not_mutation_of_real_archive':True,'all_actual_retained_archives_independently_hash_verified':True,'cloud_operation':False,'compiler_invoked':False}
 (d/'result.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({'checks':len(tests),'sha256':digest(d/'result.json')}))
if __name__=='__main__':main()
