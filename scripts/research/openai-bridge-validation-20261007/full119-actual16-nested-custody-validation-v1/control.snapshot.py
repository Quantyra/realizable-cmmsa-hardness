"""Actual receipt/pins and exact native nested custody tests; never mutates real archives."""
from pathlib import Path
import json,hashlib,tarfile
import full119_authorized16_nested_custody_v3 as active
from full119_pending16_nested_custody_v2 import Pending16Custody,Actual16Evidence
from full118_consolidated_preservation_resolver_v1 import checked
import custody_checks
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 d=H/'full119-actual16-nested-custody-validation-v1';d.mkdir(exist_ok=False);before=custody_checks.verify_local_custody;g=active.configured_guard();g.documents();tests=[]
 for p,r in g.resolver.rows.items():
  if r['kind']!='nested_complete_native':continue
  j=json.loads(Path(r['historical_index']).read_bytes());c=j['terminal_receipt']['custody'];result=g.reconcile(c['short_path'],c['repository_path'],c['remote_sha256'],c['bytes']);assert result['current_retained_complete_native_archives_verified']==(2 if 'retained_flat_archive' in r else 1);assert result['new_two_copy_custody'] is False;tests.append(dict(name='actual_exact_native_custody_honest_representation',path=str(p),result=result,passed=True));print('native_case',len(tests),flush=True)
 def reject(name,fn):
  try:fn()
  except (ValueError,FileNotFoundError,KeyError):tests.append(dict(name=name,passed=True));return
  raise AssertionError('Expected rejection: '+name)
 reject('missing_actual_receipt',lambda:Pending16Custody().documents())
 rec=d/'NON-ACTUAL-receipt-byte-mutant.json';rec.write_bytes(active.RECEIPT.read_bytes()+b'\n');reject('changed_receipt_bytes_required_strings_preserved',lambda:Actual16Evidence(rec,active.RECEIPT_PIN,active.AUTH,active.AUTH_PIN,active.USER_REPLY,active.REPLY_ID))
 auth=d/'NON-ACTUAL-authorization-byte-mutant.json';auth.write_bytes(active.AUTH.read_bytes()+b'\n');reject('changed_authorization_bytes_required_strings_preserved',lambda:Actual16Evidence(active.RECEIPT,active.RECEIPT_PIN,auth,active.AUTH_PIN,active.USER_REPLY,active.REPLY_ID))
 reject('wrong_actual_reply',lambda:Pending16Custody(Actual16Evidence(active.RECEIPT,active.RECEIPT_PIN,active.AUTH,active.AUTH_PIN,'wrong actual reply',active.REPLY_ID)).documents())
 reject('wrong_actual_reply_id',lambda:Pending16Custody(Actual16Evidence(active.RECEIPT,active.RECEIPT_PIN,active.AUTH,active.AUTH_PIN,active.USER_REPLY,'wrong actual reply id')).documents())
 rr=next(r for r in g.resolver.rows.values() if r['kind']=='nested_complete_native');jj=json.loads(Path(rr['historical_index']).read_bytes());c=jj['terminal_receipt']['custody']
 reject('wrong_native_hash',lambda:g.reconcile(c['short_path'],c['repository_path'],'0'*64,c['bytes']))
 reject('wrong_native_path',lambda:g.reconcile(c['short_path'],str(Path(c['repository_path']).with_name('unapproved.tar.gz')),c['remote_sha256'],c['bytes']))
 fixture=d/'NON-ACTUAL-retained-byte-fixture.txt';fixture.write_bytes(b'fixture exact original bytes\n');pin=sha(fixture.read_bytes());fixture.write_bytes(fixture.read_bytes()+b'!');reject('retained_byte_change_fixture_not_real_archive',lambda:checked(fixture,pin))
 # The immutable original gate remains red for a retired standalone archive; only explicit successor resolves it.
 reject('legacy_original_two_copy_gate_remains_red',lambda:before(c['short_path'],c['repository_path'],c['remote_sha256'],c['bytes']))
 assert custody_checks.verify_local_custody is before
 j=dict(actual_receipt_sha256=active.RECEIPT_PIN,actual_authorization_sha256=active.AUTH_PIN,adapter_sha256=sha(Path(active.__file__).read_bytes()),pending_adapter_sha256=active.PENDING_PIN,checks=tests,all_passed=True,no_real_archive_mutation=True,no_production_adapter_installed=True,no_fake_authorization_or_receipt=True,legacy_original_gates_unchanged=True,compiler_invoked=False)
 (d/'result.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());print(json.dumps(dict(checks=len(tests),result_sha256=sha((d/'result.json').read_bytes()),adapter_sha256=j['adapter_sha256'])))
if __name__=='__main__':main()
