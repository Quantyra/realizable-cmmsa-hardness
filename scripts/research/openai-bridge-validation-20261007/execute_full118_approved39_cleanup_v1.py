"""Execute only the explicitly authorized frozen 39-file duplicate plan."""
import hashlib,json,os,subprocess,tarfile,shutil
from datetime import datetime,timezone
from pathlib import Path
H=Path(__file__).resolve().parent
BASE=Path('C:/Users/dfred/.quantyra/builder02').resolve(strict=True)
SHORT=Path('C:/a8gcp').resolve(strict=True)
PLAN=H/'full118-settled-duplicate-archive-cleanup-plan-v1/plan.json'
PIN='78D9D0ABD067A0D1B55F68B2937E7453CE945E5A0D27B17B7B1CCD64C7D60486'
AUTH='Approve these 39 duplicates'
REPLY='call_6f682c9366ed44459369c65368325c0a'
def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest().upper()
def safe(p,base):
 p=Path(p);assert p.is_absolute() and p.resolve(strict=True)==p.absolute() and p.is_relative_to(base)
 assert p.is_file() and not p.is_symlink()
 for q in [p,*p.parents]:
  if q.is_relative_to(base):assert not (os.lstat(q).st_file_attributes&0x400),str(q)
 assert "'" not in str(p)
 return p
def retained(r):
 p=safe(r['retain_complete_native_archive'],BASE)
 assert 'full118-' not in str(p)
 assert p.stat().st_size==r['retained_archive_bytes'] and digest(p)==r['retained_archive_sha256']
 if r['retained_member'] is not None:
  with tarfile.open(p,'r:gz') as t:
   members=[x for x in t.getmembers() if x.name==r['retained_member']];assert len(members)==1 and members[0].isfile()
   m=members[0];assert m.size==r['retained_member_bytes'];h=hashlib.sha256();f=t.extractfile(m)
   for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
   assert h.hexdigest().upper()==r['retained_member_sha256']==r['sha256']
 return p
def terminal(r):
 for key in ['terminal_receipt','independent_stop']:
  p=safe(r[key],BASE);assert digest(p)==r[key+'_sha256']
 t=json.loads(Path(r['terminal_receipt']).read_bytes());s=json.loads(Path(r['independent_stop']).read_bytes())
 assert t['run']==s['run']==r['run'] and t['terminal']['native_terminal'] is True
 assert s['independent']['status']=='TERMINATED' and str(s['independent']['id'])=='7237681467779354904'
def main():
 assert digest(PLAN)==PIN;j=json.loads(PLAN.read_bytes());assert j['count']==len(j['files'])==39 and j['total_bytes']==509908701
 assert len({str(Path(r['remove']).resolve()) for r in j['files']})==39
 d=H/'full118-approved39-cleanup-receipt-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n')
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());(d/'approved-plan.json').write_bytes(PLAN.read_bytes())
 auth=dict(authorization=AUTH,authorization_received=True,reply_reference=REPLY,relayed_by='root',approved_plan_sha256=PIN,scope_count=39,scope_bytes=509908701)
 (d/'authorization.json').write_text(json.dumps(auth,indent=2)+'\n',encoding='utf-8');before=shutil.disk_usage(BASE).free
 # Verify the entire exact set before the first destructive action.
 for r in j['files']:
  p=safe(r['remove'],SHORT if r['kind']=='short_complete_native_duplicate' else BASE)
  assert 'full118-' not in str(p) and p.stat().st_size==r['bytes'] and digest(p)==r['sha256'];terminal(r);retained(r)
 rows=[]
 for i,r in enumerate(j['files']):
  p=safe(r['remove'],SHORT if r['kind']=='short_complete_native_duplicate' else BASE)
  assert p.stat().st_size==r['bytes'] and digest(p)==r['sha256'];terminal(r);keep=retained(r)
  command="Remove-Item -LiteralPath '"+str(p)+"' -Force -ErrorAction Stop"
  result=subprocess.run(['C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe','-NoProfile','-NonInteractive','-Command',command],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
  (d/f'{i:02}.stdout').write_bytes(result.stdout);(d/f'{i:02}.stderr').write_bytes(result.stderr)
  assert result.returncode==0 and not p.exists();retained(r)
  row=dict(removed=str(p),retained=str(keep),bytes=r['bytes'],sha256=r['sha256'],retained_archive_sha256=r['retained_archive_sha256'],retained_member_sha256=r['retained_member_sha256'],retained_verified_after=True,native_remove_exit=result.returncode)
  rows.append(row)
  with (d/'completed.jsonl').open('ab') as f:f.write((json.dumps(row)+'\n').encode())
  print(json.dumps(dict(completed=len(rows),count=39)),flush=True)
 for r in j['files']:assert not Path(r['remove']).exists();retained(r);terminal(r)
 receipt=dict(**auth,authorization_sha256=digest(d/'authorization.json'),only_exact_approved_files=True,files_deleted=True,files=rows,count=39,total_bytes=509908701,all_retained_originals_and_members_verified_after=True,historical_receipts_unchanged=True,free_before=before,free_after=shutil.disk_usage(BASE).free,required_local_bytes=1803550720,cloud_operation=False,compiler_invoked=False,extra_files_deleted=False)
 # approved_plan_sha256 is already in the authorization dictionary.
 receipt['approved_plan_sha256']=PIN
 (d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(receipt_sha256=digest(d/'receipt.json'),free_after=receipt['free_after'])),flush=True)
if __name__=='__main__':main()
