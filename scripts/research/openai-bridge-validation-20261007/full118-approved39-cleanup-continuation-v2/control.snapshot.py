"""Disjoint continuation of the approved set after preserved memory failure."""
import sys,json,hashlib,tarfile,subprocess,shutil
from pathlib import Path
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
import execute_full118_approved39_cleanup_v1 as old
def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(16384),b''):h.update(b)
 return h.hexdigest().upper()
def retained(r):
 p=old.safe(r['retain_complete_native_archive'],old.BASE)
 assert 'full118-' not in str(p)
 assert p.stat().st_size==r['retained_archive_bytes'] and digest(p)==r['retained_archive_sha256']
 if r['retained_member'] is not None:
  count=0
  with tarfile.open(p,'r|gz',bufsize=16384) as t:
   for m in t:
    if m.name!=r['retained_member']:continue
    count+=1;assert m.isfile() and m.size==r['retained_member_bytes'];h=hashlib.sha256();f=t.extractfile(m)
    for b in iter(lambda:f.read(16384),b''):h.update(b)
    assert h.hexdigest().upper()==r['retained_member_sha256']==r['sha256']
  assert count==1
 return p
old.digest=digest
def main():
 first=H/'full118-approved39-cleanup-receipt-v1';assert not (first/'receipt.json').exists()
 assert digest(first/'approved-plan.json')==old.PIN==digest(old.PLAN)
 assert (first/'control.snapshot.py').read_bytes()==Path(old.__file__).read_bytes()
 auth=json.loads((first/'authorization.json').read_bytes());assert auth['authorization']==old.AUTH and auth['reply_reference']==old.REPLY and auth['authorization_received'] is True
 plan=json.loads(old.PLAN.read_bytes());rows=[json.loads(line) for line in (first/'completed.jsonl').read_text().splitlines()]
 assert len(rows)==2 and len({r['removed'] for r in rows})==2
 bypath={str(Path(r['remove'])):r for r in plan['files']};assert len(bypath)==39
 d=H/'full118-approved39-cleanup-continuation-v2';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 (d/'authorization.json').write_bytes((first/'authorization.json').read_bytes());(d/'approved-plan.json').write_bytes(old.PLAN.read_bytes())
 before=shutil.disk_usage(old.BASE).free
 for done in rows:
  r=bypath[done['removed']];assert not Path(done['removed']).exists() and done['sha256']==r['sha256'] and done['bytes']==r['bytes'] and done['retained_verified_after'] is True
  retained(r);old.terminal(r)
 remaining=[r for r in plan['files'] if str(Path(r['remove'])) not in {x['removed'] for x in rows}];assert len(remaining)==37
 for r in remaining:
  p=old.safe(r['remove'],old.SHORT if r['kind']=='short_complete_native_duplicate' else old.BASE)
  assert 'full118-' not in str(p) and p.stat().st_size==r['bytes'] and digest(p)==r['sha256'];retained(r);old.terminal(r)
  print(json.dumps(dict(preverified_remaining=r['number'],path=str(p))),flush=True)
 for i,r in enumerate(remaining):
  p=old.safe(r['remove'],old.SHORT if r['kind']=='short_complete_native_duplicate' else old.BASE)
  assert p.stat().st_size==r['bytes'] and digest(p)==r['sha256'];keep=retained(r);old.terminal(r)
  command="Remove-Item -LiteralPath '"+str(p)+"' -Force -ErrorAction Stop"
  x=subprocess.run(['C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe','-NoProfile','-NonInteractive','-Command',command],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
  (d/f'{i:02}.stdout').write_bytes(x.stdout);(d/f'{i:02}.stderr').write_bytes(x.stderr);assert x.returncode==0 and not p.exists();retained(r)
  done=dict(removed=str(p),retained=str(keep),bytes=r['bytes'],sha256=r['sha256'],retained_archive_sha256=r['retained_archive_sha256'],retained_member_sha256=r['retained_member_sha256'],retained_verified_after=True,native_remove_exit=x.returncode)
  rows.append(done)
  with (d/'completed.jsonl').open('ab') as f:f.write((json.dumps(done)+'\n').encode())
  print(json.dumps(dict(completed_total=len(rows),count=39)),flush=True)
 for r in plan['files']:assert not Path(r['remove']).exists();retained(r);old.terminal(r)
 receipt=dict(**auth,authorization_sha256=digest(d/'authorization.json'),only_exact_approved_files=True,files_deleted=True,files=rows,count=39,total_bytes=509908701,all_retained_originals_and_members_verified_after=True,historical_receipts_unchanged=True,original_partial_directory=str(first),original_partial_memory_failure_preserved=True,free_before_continuation=before,free_after=shutil.disk_usage(old.BASE).free,required_local_bytes=1803550720,cloud_operation=False,compiler_invoked=False,extra_files_deleted=False)
 (d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(receipt_sha256=digest(d/'receipt.json'),free_after=receipt['free_after'])),flush=True)
if __name__=='__main__':main()
