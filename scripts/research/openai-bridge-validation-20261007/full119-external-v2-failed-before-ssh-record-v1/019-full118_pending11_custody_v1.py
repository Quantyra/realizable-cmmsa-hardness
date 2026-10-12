"""Disjoint fail-closed preparation for eleven pending exact archive retirements."""
from dataclasses import dataclass
from pathlib import Path
import full118_authorized39_custody_v2 as previous
from full115_cumulative_cleanup_custody_v2 import checked_json,ORIGINAL
import custody_checks
HERE=Path(__file__).resolve().parent
PLAN=HERE/'full118-next-eleven-settled-archives-plan-v2/plan.json'
PLAN_PIN='31E0A8A13955D4A7201AEC78D72FA0E793D3FD446B51C277642A8EA67B5C674F'
PREVIOUS_PIN='64105A366D29A03931798DB6E9F65E709A2CB39EAE8F1045176F16BA36073DFB'
STOP=Path('C:/Users/dfred/.quantyra/builder02/full118-exact-real-complex-operators-repair8-resource02/checks/20261012T023543679265Z/vm-termination.json')
STOP_PIN='85D67B53B8CFA892E2982F6D88D6E7F0665029068253E9D1AFF59AE047A83A68'
@dataclass(frozen=True)
class Actual11Receipt:
 path:Path
 sha256:str
 authorization_path:Path
 authorization_sha256:str
 user_reply:str
 source_reply_id:str
 def __post_init__(self):
  if not self.user_reply.strip() or not self.source_reply_id.strip():raise ValueError('Actual explicit user reply and source ID required')
  for p in [self.path,self.authorization_path]:
   if not Path(p).resolve().is_relative_to(HERE):raise ValueError('Actual pinned evidence must be retained on this evidence surface')
  checked_json(self.path,self.sha256);checked_json(self.authorization_path,self.authorization_sha256)
class Pending11Custody:
 def __init__(self,actual=None):
  if actual is not None and not isinstance(actual,Actual11Receipt):raise TypeError('Actual complete pinned receipt required')
  self.actual=actual
 def documents(self):
  if custody_checks.digest(Path(previous.__file__))!=PREVIOUS_PIN:raise ValueError('Prior actual39 adapter changed')
  plan=checked_json(PLAN,PLAN_PIN)
  if plan['file_count']!=11 or len(plan['files'])!=11 or plan['total_remove_bytes']!=156006852:raise ValueError('Exact frozen plan changed')
  if self.actual is None:raise ValueError('Pending eleven scope has no actual user authorization/deletion receipt')
  receipt=checked_json(self.actual.path,self.actual.sha256);auth=checked_json(self.actual.authorization_path,self.actual.authorization_sha256)
  if (auth.get('approved') is not True or auth.get('explicit_user_authorization') is not True or auth.get('approved_plan_sha256')!=PLAN_PIN or auth.get('user_reply')!=self.actual.user_reply or auth.get('source_reply_id')!=self.actual.source_reply_id):raise ValueError('Actual exact user authorization required')
  if (receipt.get('plan_sha256')!=PLAN_PIN or receipt.get('authorization_sha256')!=self.actual.authorization_sha256 or receipt.get('actual_user_reply')!=self.actual.user_reply or receipt.get('source_reply_id')!=self.actual.source_reply_id or receipt.get('complete') is not True or receipt.get('retained_originals_unchanged') is not True or receipt.get('removed_count')!=11 or receipt.get('removed_bytes')!=156006852):raise ValueError('Complete exact authorized receipt required')
  approved={Path(r['remove']).resolve():r for r in plan['files']};done={Path(r['path']).resolve():r for r in receipt['removed']}
  if len(approved)!=11 or len(receipt['removed'])!=11 or set(approved)!=set(done):raise ValueError('Exactly all eleven path identities required')
  for p,r in approved.items():
   x=done[p];q=Path(r['retained_archive'])
   if (p.exists() or Path(x['retained_archive']).resolve()!=q.resolve() or x.get('bytes')!=r['remove_bytes'] or x.get('sha256')!=r['remove_sha256'] or x.get('native_exit')!=0 or x.get('retained_verified_after') is not True or x.get('retained_sha256')!=r['retained_archive_sha256']):raise ValueError('Approved absent-path and retained-copy receipt identity required')
   if q.stat().st_size!=r['retained_archive_bytes'] or custody_checks.digest(q)!=r['retained_archive_sha256']:raise ValueError('Retained complete/partial archive bytes changed')
   for field in ['retained_terminal_receipt','retained_index','preservation_record']:
    if field in r:checked_json(r[field],r[field+'_sha256'])
  stop=checked_json(STOP,STOP_PIN)
  if stop['independent']['status']!='TERMINATED' or str(stop['independent']['id'])!='7237681467779354904':raise ValueError('Exact independently stopped owned VM required')
  previous.configured_guard().documents()
  return approved,receipt
 def reconcile(self,short_path,repository_path,remote_sha256,remote_bytes):
  short,retained=Path(short_path),Path(repository_path);plan=checked_json(PLAN,PLAN_PIN)
  new={Path(r['remove']).resolve():r for r in plan['files'] if 'archive_terminal_member_sha256' in r}
  if short.exists() or short.resolve() not in new:return previous.configured_guard().reconcile(short,retained,remote_sha256,remote_bytes)
  approved,_=self.documents();r=approved[short.resolve()]
  if (retained.resolve()!=Path(r['retained_archive']).resolve() or remote_sha256!=r['remove_sha256'] or type(remote_bytes) is not int or remote_bytes!=r['remove_bytes']):raise ValueError('Exact current consumption archive/path identities required')
  terminal=checked_json(r['retained_terminal_receipt'],r['retained_terminal_receipt_sha256']);old=terminal['custody']
  if Path(old['short_path']).resolve()!=short.resolve() or Path(old['repository_path']).resolve()!=retained.resolve() or old['remote_sha256']!=remote_sha256 or old['bytes']!=remote_bytes:raise ValueError('Historical exact consumption custody identities changed')
  return dict(short_path=str(short),repository_path=str(retained),remote_sha256=remote_sha256,repository_sha256=remote_sha256,bytes=remote_bytes,current_retained_copies_verified=1,new_two_copy_custody=False,historical_two_copy_receipt_preserved=True,short_copy_removed_with_explicit_authorization=True,authorized_cleanup_plan_sha256=PLAN_PIN,authorized_cleanup_receipt_sha256=self.actual.sha256)
 def retired_portable_payload(self,path):
  approved,_=self.documents();r=approved[Path(path).resolve()]
  if 'all110_original_members_exactly_retained' not in r:raise ValueError('Only exact terminal portable payload retirement is supported')
  import tarfile,hashlib
  with tarfile.open(r['retained_archive'],'r:gz') as t:
   for x in r['all110_original_members_exactly_retained']:
    b=t.extractfile(x['retained_member']).read()
    if len(b)!=x['bytes'] or hashlib.sha256(b).hexdigest().upper()!=x['sha256']:raise ValueError('Retained final archive member bytes changed')
  return dict(retired_path=str(path),retained_final_archive=r['retained_archive'],retained_final_sha256=r['retained_archive_sha256'],exact_original_members=110,historical_terminal_index_unchanged=True,retirement_receipt_sha256=self.actual.sha256)
def activate(actual):
 guard=Pending11Custody(actual);guard.documents()
 if custody_checks.verify_local_custody is not ORIGINAL:raise ValueError('Another custody adapter already installed')
 custody_checks.verify_local_custody=guard.reconcile
 return guard
