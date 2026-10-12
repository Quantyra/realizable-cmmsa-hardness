"""Read-only exact preservation resolver preparation. Never installs a custody adapter."""
import json,hashlib,tarfile
from pathlib import Path
from contextlib import contextmanager
H=Path(__file__).resolve().parent
PLAN=H/'full118-consolidated-settled-preservation-plan-v2/plan.json'
PLAN_PIN='8279E719DB5AC3F4B5252A0CF1E86597BD46051949BC9212D9E6A739CA306CB8'
def digest(f):
 h=hashlib.sha256();n=0
 while True:
  b=f.read(1024*1024)
  if not b:break
  h.update(b);n+=len(b)
 return h.hexdigest().upper(),n
def checked(p,pin,size=None):
 with Path(p).open('rb') as f:q,n=digest(f)
 if q!=pin or (size is not None and n!=size):raise ValueError('Whole retained evidence bytes changed')
 return n
class PreparedResolver:
 def __init__(self):
  checked(PLAN,PLAN_PIN);self.plan=json.loads(PLAN.read_bytes());self.rows={Path(r['remove']).resolve():r for r in self.plan['files']}
  if len(self.rows)!=16:raise ValueError('Exact plan path identities changed')
 def row(self,path,sha,size):
  p=Path(path).resolve()
  if p not in self.rows:raise ValueError('Path is outside the exact prepared scope')
  r=self.rows[p]
  if r['remove_sha256']!=sha or type(size) is not int or r['remove_bytes']!=size:raise ValueError('Exact original archive identity required')
  checked(r['historical_index'],r['historical_index_sha256']);checked(r['retained_archive'],r['retained_archive_sha256'],r['retained_archive_bytes']);checked(r['complete_native_members_reference'],r['complete_native_members_reference_sha256'])
  return r
 @contextmanager
 def complete_archive(self,path,sha,size):
  r=self.row(path,sha,size)
  if r['kind']=='contained_earlier_portable_payload':raise ValueError('Contained payload resolves members, not identical archive bytes')
  if r['kind']=='nested_complete_native':
   with tarfile.open(r['retained_archive'],'r:gz') as outer:
    entry=outer.getmember(r['retained_member'])
    if not entry.isfile() or entry.size!=size:raise ValueError('Exact complete nested archive member required')
    if digest(outer.extractfile(entry))!=(sha,size):raise ValueError('Complete nested native bytes changed')
    yield outer.extractfile(entry)
  else:
   checked(r['retained_archive'],sha,size)
   with Path(r['retained_archive']).open('rb') as f:yield f
 @contextmanager
 def preserved_original_member(self,path,sha,size,member):
  r=self.row(path,sha,size)
  if r['kind']!='contained_earlier_portable_payload':raise ValueError('Exact subset payload row required')
  mapping=json.loads(Path(r['complete_native_members_reference']).read_bytes());matches=[x for x in mapping if x['retired_member']==member]
  if len(matches)!=1:raise ValueError('Exact original member identity required')
  x=matches[0]
  with tarfile.open(r['retained_archive'],'r:gz') as t:
   entry=t.getmember(x['retained_member'])
   if not entry.isfile() or digest(t.extractfile(entry))!=(x['sha256'],x['bytes']):raise ValueError('Exact retained original member bytes changed')
   yield t.extractfile(entry)
 def require_actual_retirement(self,receipt_path=None,receipt_pin=None,authorization_path=None,authorization_pin=None):
  # No guessed future receipt or approval is accepted by this preparation.
  if None in (receipt_path,receipt_pin,authorization_path,authorization_pin):raise ValueError('Actual complete receipt and explicit authorization bytes required')
  checked(receipt_path,receipt_pin);checked(authorization_path,authorization_pin)
  receipt=json.loads(Path(receipt_path).read_bytes());auth=json.loads(Path(authorization_path).read_bytes())
  if auth.get('approved') is not True or auth.get('approved_plan_sha256')!=PLAN_PIN or not auth.get('user_reply','').strip() or not auth.get('source_reply_id','').strip():raise ValueError('Actual exact user authorization required')
  if receipt.get('complete') is not True or receipt.get('plan_sha256')!=PLAN_PIN or receipt.get('authorization_sha256')!=authorization_pin or receipt.get('removed_count')!=16 or receipt.get('removed_bytes')!=self.plan['total_remove_bytes']:raise ValueError('Actual exact complete retirement receipt required')
  done={Path(x['path']).resolve():x for x in receipt['removed']}
  if set(done)!=set(self.rows):raise ValueError('Receipt must cover exactly the authorized paths')
  for p,r in self.rows.items():
   x=done[p]
   if p.exists() or x.get('sha256')!=r['remove_sha256'] or x.get('bytes')!=r['remove_bytes'] or x.get('native_exit')!=0 or x.get('retained_verified_after') is not True:raise ValueError('Actual absent path and exact preservation required')
   self.row(p,r['remove_sha256'],r['remove_bytes'])
  return receipt
