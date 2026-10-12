"""Pending exact eleven-file cleanup. Execution requires actual user authorization."""
import sys,json,hashlib,tarfile,subprocess,shutil
from pathlib import Path
H=Path(__file__).resolve().parent
PLAN=H/'full118-next-eleven-settled-archives-plan-v2/plan.json'
PIN='31E0A8A13955D4A7201AEC78D72FA0E793D3FD446B51C277642A8EA67B5C674F'
def digest(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest().upper()
def load_plan():
 assert digest(PLAN)==PIN
 j=json.loads(PLAN.read_bytes());assert j['file_count']==11 and j['total_remove_bytes']==156006852 and not j['approval_received']
 return j
def authorization(a):
 assert a.get('approved') is True and a.get('approved_plan_sha256')==PIN
 assert isinstance(a.get('user_reply'),str) and a['user_reply'].strip()
 assert isinstance(a.get('source_reply_id'),str) and a['source_reply_id'].strip()
 assert a.get('explicit_user_authorization') is True
 return a
def identities(r,require_remove):
 p=Path(r['remove']);q=Path(r['retained_archive'])
 allowed=p.parent==Path('C:/a8gcp') or p==H/'full115-native-terminal-custody-v1/complete-originals.tar.gz'
 assert allowed and p.absolute()==p and q!=p
 if require_remove:
  assert p.resolve(strict=True)==p and p.is_file() and not p.is_symlink()
  assert p.stat().st_size==r['remove_bytes'] and digest(p)==r['remove_sha256']
 else:assert not p.exists()
 assert q.resolve(strict=True)==q and q.is_file() and not q.is_symlink()
 assert q.stat().st_size==r['retained_archive_bytes'] and digest(q)==r['retained_archive_sha256']
 for f in [p,q]:
  for ancestor in f.parents:
   if ancestor.exists():assert not ancestor.is_symlink()
 for field in ['retained_terminal_receipt','retained_index','preservation_record']:
  if field in r:assert digest(Path(r[field]))==r[field+'_sha256']
 return p,q
def member_checks(r,q):
 if r.get('partial_failed_transfer_not_full_native_archive'):return
 with tarfile.open(q,'r:gz') as t:
  ms=t.getmembers();assert all(m.isfile() for m in ms) and len(ms)==len({m.name for m in ms})
  if 'archive_terminal_member_sha256' in r:
   assert len(ms)==r['archive_member_count'];b=t.extractfile('terminal.json').read();assert hashlib.sha256(b).hexdigest().upper()==r['archive_terminal_member_sha256'];assert json.loads(b)
  for x in r.get('all110_original_members_exactly_retained',[]):
   b=t.extractfile(x['retained_member']).read();assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest().upper()==x['sha256']
def main():
 j=load_plan()
 if sys.argv[1:]==['--inspect']:
  for r in j['files']:p,q=identities(r,True);member_checks(r,q)
  print(json.dumps({'read_only':True,'files':11,'bytes':156006852,'all_current_and_retained_hashes_verified':True}));return
 assert len(sys.argv)==3 and sys.argv[1]=='--execute'
 ap=Path(sys.argv[2]).resolve(strict=True);assert ap.is_relative_to(H)
 authbytes=ap.read_bytes();a=authorization(json.loads(authbytes))
 for r in j['files']:p,q=identities(r,True);member_checks(r,q)
 d=H/'full118-approved11-cleanup-execution-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'plan.snapshot.json').write_bytes(PLAN.read_bytes());(d/'authorization.snapshot.json').write_bytes(authbytes);(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 receipt={'plan_sha256':PIN,'authorization_sha256':hashlib.sha256(authbytes).hexdigest().upper(),'actual_user_reply':a['user_reply'],'source_reply_id':a['source_reply_id'],'approved_file_count':11,'approved_bytes':156006852,'removed':[],'free_before':shutil.disk_usage(H).free,'compiler_invoked':False,'cloud_action':False,'retained_originals_unchanged':False}
 try:
  for i,r in enumerate(j['files']):
   assert ap.read_bytes()==authbytes and digest(PLAN)==PIN
   p,q=identities(r,True);member_checks(r,q)
   literal=str(p).replace("'","''");cmd="Remove-Item -LiteralPath '"+literal+"' -ErrorAction Stop"
   x=subprocess.run(['C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe','-NoProfile','-NonInteractive','-Command',cmd],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
   (d/f'{i:02d}.stdout').write_bytes(x.stdout);(d/f'{i:02d}.stderr').write_bytes(x.stderr);assert x.returncode==0
   identities(r,False);member_checks(r,q);receipt['removed'].append({'path':str(p),'bytes':r['remove_bytes'],'sha256':r['remove_sha256'],'native_exit':x.returncode,'retained_archive':str(q),'retained_sha256':digest(q),'retained_verified_after':True})
   (d/'partial-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
  for r in j['files']:p,q=identities(r,False);member_checks(r,q)
  receipt.update(retained_originals_unchanged=True,complete=True,free_after=shutil.disk_usage(H).free,removed_count=len(receipt['removed']),removed_bytes=sum(x['bytes'] for x in receipt['removed']),honest_one_retained_complete_archive_for_eight_consumption_copies=True,failed_partial_bytes_retained=True,all110_retired_terminal_members_in_retained_final=True)
  (d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8');print(json.dumps({'receipt_sha256':digest(d/'receipt.json'),'removed_count':11,'removed_bytes':receipt['removed_bytes'],'free_after':receipt['free_after']}))
 except BaseException as e:
  receipt.update(complete=False,failure_type=type(e).__name__,failure=str(e));(d/'failed-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8');raise
if __name__=='__main__':main()
