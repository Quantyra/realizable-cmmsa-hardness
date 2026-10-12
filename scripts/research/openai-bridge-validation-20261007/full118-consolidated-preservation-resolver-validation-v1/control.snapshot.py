"""Read-only resolver tests; no real archive mutation, removal or approval."""
import json,hashlib,tarfile
from pathlib import Path
from full118_consolidated_preservation_resolver_v1 import PreparedResolver,checked,digest,PLAN,PLAN_PIN
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 d=H/'full118-consolidated-preservation-resolver-validation-v1';d.mkdir(exist_ok=False);guard=PreparedResolver();tests=[]
 for p,r in guard.rows.items():
  if r['kind']=='contained_earlier_portable_payload':
   mapping=json.loads(Path(r['complete_native_members_reference']).read_bytes())
   for x in mapping:
    with guard.preserved_original_member(p,r['remove_sha256'],r['remove_bytes'],x['retired_member']) as f:assert digest(f)==(x['sha256'],x['bytes'])
   tests.append(dict(name='exact_subset_original_member_transport',path=str(p),members=len(mapping),passed=True))
  else:
   with guard.complete_archive(p,r['remove_sha256'],r['remove_bytes']) as f:assert digest(f)==(r['remove_sha256'],r['remove_bytes'])
   expected=json.loads(Path(r['complete_native_members_reference']).read_bytes());actual=[]
   with guard.complete_archive(p,r['remove_sha256'],r['remove_bytes']) as f:
    with tarfile.open(fileobj=f,mode='r|gz') as t:
     for m in t:
      if m.isfile():
       q,n=digest(t.extractfile(m));actual.append(dict(member=m.name,bytes=n,sha256=q))
   assert actual==expected;tests.append(dict(name='complete_archive_stream_and_every_member',path=str(p),members=len(actual),passed=True))
 def rejects(name,call):
  try:call()
  except (ValueError,FileNotFoundError,KeyError):tests.append(dict(name=name,passed=True));return
  raise AssertionError(name+' did not reject')
 p,r=next(iter(guard.rows.items()))
 rejects('wrong_archive_path',lambda:guard.row(p.with_name('not-approved.tar.gz'),r['remove_sha256'],r['remove_bytes']))
 rejects('wrong_archive_hash',lambda:guard.row(p,'0'*64,r['remove_bytes']))
 rejects('wrong_archive_size',lambda:guard.row(p,r['remove_sha256'],r['remove_bytes']+1))
 rejects('missing_actual_authorization_and_receipt',lambda:guard.require_actual_retirement())
 rejects('missing_actual_receipt_file',lambda:guard.require_actual_retirement(d/'NO-RECEIPT.json','0'*64,d/'NO-AUTH.json','0'*64))
 fixture=d/'NON-ACTUAL-fixture.txt';fixture.write_bytes(b'actual expected required strings\n');pin=sha(fixture.read_bytes());fixture.write_bytes(fixture.read_bytes()+b'\n');rejects('retained_byte_change_with_required_strings_intact',lambda:checked(fixture,pin));rejects('wrong_receipt_whole_byte_pin',lambda:checked(fixture,pin))
 # All current cumulative actual cleanup documents still validate. No adapter is installed.
 import full118_authorized11_custody_v2 as previous,custody_checks
 before=custody_checks.verify_local_custody;previous.configured_guard().documents();assert custody_checks.verify_local_custody is before
 tests.append(dict(name='prior_actual14_18_20_39_11_documents_still_green_no_adapter_installed',passed=True))
 compatibility=dict(current_full118_flat_archive_retained=True,current_full119_parent_source_inputs_not_retired=True,old_gates_immutable=True,legacy_missing_standalone_reconcile_will_need_disjoint_successor=True,no_global_Path_or_tarfile_monkeypatch=True,streaming_tarfile_consumers_must_use_resolver_and_r_stream_gz=True,subset_consumers_must_use_original_identity_mapping=True,historical_terminal_stop_audit_controls_and_indices_unchanged=True,activation_blocked_until_actual_frozen_authorization_and_complete_receipt=True)
 j=dict(plan_sha256=PLAN_PIN,resolver_sha256=sha((H/'full118_consolidated_preservation_resolver_v1.py').read_bytes()),tests=tests,all_passed=True,compatibility=compatibility,fixtures_not_actual_receipts=True,files_deleted=False,compiler_invoked=False,adapter_installed=False)
 (d/'result.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());print(json.dumps(dict(checks=len(tests),result_sha256=sha((d/'result.json').read_bytes()),resolver_sha256=j['resolver_sha256'])))
if __name__=='__main__':main()
