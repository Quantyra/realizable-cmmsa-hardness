"""Disjoint actual-receipt-bound nested custody; never infers approval."""
from dataclasses import dataclass
from pathlib import Path
import json
import full118_authorized11_custody_v2 as previous
import full118_authorized39_custody_v2 as old39
import full115_cumulative_actual_receipts_v1 as old14_18
import full115_cumulative_cleanup_custody_v2 as oldbase
from full115_cumulative_cleanup_custody_v2 import checked_json,ORIGINAL,VM_ID
from full118_consolidated_preservation_resolver_v1 import PreparedResolver,PLAN_PIN,checked,digest
import custody_checks
H=Path(__file__).resolve().parent
PREVIOUS_PIN='8789E6B4F7867299E94A8C92A3F0044A42AB5D99C1F35DF1AD98F54B9F7AB644'
RESOLVER_PIN='64CF6B8E3A0151713DA1EEEDA63DCE2A0687D612E86370948574487C01C7D090'
@dataclass(frozen=True)
class Actual16Evidence:
 receipt:Path
 receipt_sha256:str
 authorization:Path
 authorization_sha256:str
 user_reply:str
 source_reply_id:str
 def __post_init__(self):
  if not self.user_reply.strip() or not self.source_reply_id.strip():raise ValueError('Actual explicit reply identity required')
  for p in [self.receipt,self.authorization]:
   if not Path(p).resolve().is_relative_to(H):raise ValueError('Actual retained evidence must be on campaign surface')
  checked(self.receipt,self.receipt_sha256);checked(self.authorization,self.authorization_sha256)
class Pending16Custody:
 def __init__(self,actual=None):
  if actual is not None and not isinstance(actual,Actual16Evidence):raise TypeError('Actual complete pinned evidence required')
  self.actual=actual;self.resolver=PreparedResolver()
 def documents(self):
  checked(Path(previous.__file__),PREVIOUS_PIN);checked(H/'full118_consolidated_preservation_resolver_v1.py',RESOLVER_PIN)
  if self.actual is None:raise ValueError('Exact16 cleanup has no actual complete pinned receipt bound')
  a=self.actual;r=self.resolver.require_actual_retirement(a.receipt,a.receipt_sha256,a.authorization,a.authorization_sha256);auth=json.loads(Path(a.authorization).read_bytes())
  if (auth.get('user_reply')!=a.user_reply or auth.get('source_reply_id')!=a.source_reply_id or r.get('actual_user_reply')!=a.user_reply or r.get('source_reply_id')!=a.source_reply_id):raise ValueError('Actual reply and complete receipt identity differ')
  previous.configured_guard().documents();return r
 def old_short_authorization(self,short,retained,remote_sha256,remote_bytes):
  p14=checked_json(oldbase.PLAN14,oldbase.PIN14);p18=checked_json(oldbase.PLAN18,oldbase.PIN18);earlier={Path(r['remove']).resolve() for p in [p14,p18] for r in p['files']}
  if short.resolve() in earlier:
   plans,receipt,planpin,receiptpin=old14_18.configured_guard().documents(short.resolve())
   if receipt.get('approved_plan_sha256')!=planpin or receipt.get('only_exact_approved_files') is not True:raise ValueError('Exact historical short authorization required')
   done={Path(r['removed']).resolve():r for r in receipt['files']}
   if set(done)!=set(plans) or len(done)!=len(receipt['files']):raise ValueError('Complete historical short receipt required')
   for path,row in plans.items():
    x=done[path]
    if path.exists() or Path(x['retained']).resolve()!=Path(row['retain_original']).resolve() or x['sha256']!=row['sha256'] or x['bytes']!=row['bytes'] or x.get('retained_verified_after') is not True:raise ValueError('Historical short cleanup receipt row changed')
   r=plans[short.resolve()];original=r['retain_original'];s=r['sha256'];n=r['bytes']
  else:
   plans,receipt=old39.configured_guard().documents()
   if short.resolve() not in plans or plans[short.resolve()]['kind']!='short_complete_native_duplicate':raise ValueError('Missing historical short is outside actual prior approved scope')
   r=plans[short.resolve()];original=r['retain_complete_native_archive'];s=r['sha256'];n=r['bytes']
  if (Path(original).resolve()!=retained.resolve() or s!=remote_sha256 or n!=remote_bytes):raise ValueError('Historical approved short/long pair identity changed')
  terminal=checked_json(r['terminal_receipt'],r['terminal_receipt_sha256']);stop=checked_json(r['independent_stop'],r['independent_stop_sha256']);c=terminal['custody']
  if (terminal['terminal']['native_terminal'] is not True or stop['independent']['status']!='TERMINATED' or str(stop['independent']['id'])!=VM_ID or Path(c['short_path']).resolve()!=short.resolve() or Path(c['repository_path']).resolve()!=retained.resolve() or c['remote_sha256']!=remote_sha256 or c['bytes']!=remote_bytes):raise ValueError('Exact historical native terminal/stop/pair required')
 def reconcile(self,short_path,repository_path,remote_sha256,remote_bytes):
  short,retained=Path(short_path),Path(repository_path);rows=self.resolver.rows;key=short.resolve() if short.resolve() in rows else retained.resolve()
  if key not in rows or rows[key]['kind']!='nested_complete_native':return previous.configured_guard().reconcile(short,retained,remote_sha256,remote_bytes)
  self.documents();r=rows[key];self.resolver.row(key,remote_sha256,remote_bytes);j=checked_json(r['historical_index'],r['historical_index_sha256']);c=j['terminal_receipt']['custody'];stop=j.get('independent_stop',j.get('historical_independent_termination'))
  if (Path(c['short_path']).resolve()!=short.resolve() or Path(c['repository_path']).resolve()!=retained.resolve() or c['remote_sha256']!=remote_sha256 or c['bytes']!=remote_bytes or j['terminal_receipt']['terminal']['native_terminal'] is not True or stop['independent']['status']!='TERMINATED' or str(stop['independent']['id'])!=VM_ID):raise ValueError('Exact immutable original native identity required')
  if short.exists():raise ValueError('Approved short path must remain absent')
  if key==retained.resolve():self.old_short_authorization(short,retained,remote_sha256,remote_bytes)
  with self.resolver.complete_archive(key,remote_sha256,remote_bytes) as f:
   if digest(f)!=(remote_sha256,remote_bytes):raise ValueError('Retained complete native stream changed')
  flat='retained_flat_archive' in r
  if flat:checked(r['retained_flat_archive'],remote_sha256,remote_bytes)
  return dict(short_path=str(short),repository_path=str(retained),remote_sha256=remote_sha256,repository_sha256=remote_sha256,bytes=remote_bytes,current_retained_complete_native_archives_verified=2 if flat else 1,retained_representation='flat plus exact nested archive' if flat else 'one exact complete archive nested inside portable custody',retained_portable_payload=r['retained_archive'],retained_portable_payload_sha256=r['retained_archive_sha256'],retained_native_member=r['retained_member'],historical_two_copy_receipt_preserved=True,new_two_copy_custody=False,authorized_cleanup_plan_sha256=PLAN_PIN,authorized_cleanup_receipt_sha256=self.actual.receipt_sha256)
 def complete_archive(self,path,sha,size):
  self.documents();return self.resolver.complete_archive(path,sha,size)
 def preserved_original_member(self,path,sha,size,member):
  self.documents();return self.resolver.preserved_original_member(path,sha,size,member)
def activate(actual):
 guard=Pending16Custody(actual);guard.documents()
 if custody_checks.verify_local_custody is not ORIGINAL:raise ValueError('Another adapter already installed')
 custody_checks.verify_local_custody=guard.reconcile;return guard
