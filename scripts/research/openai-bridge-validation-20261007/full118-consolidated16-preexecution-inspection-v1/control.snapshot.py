"""Exact16 executor preparation. Actual frozen authorization is required before mutation."""
import argparse,json,hashlib,subprocess,tarfile,shutil
from pathlib import Path
from full118_consolidated_preservation_resolver_v1 import PreparedResolver,PLAN,PLAN_PIN,checked,digest
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def safe(p):
 p=Path(p);q=p.resolve()
 if not (q.is_relative_to(Path('C:/Users/dfred/.quantyra').resolve()) or q.is_relative_to(Path('C:/a8gcp').resolve())):raise ValueError('Exact resolved target escapes retained campaign roots')
 for x in [p,*p.parents]:
  if x.is_symlink() or x.is_junction():raise ValueError('Symlink/junction target or parent rejected')
 if not p.is_file():raise ValueError('Exact existing file required')
 return q

def verify(guard,p,r):
 safe(p);checked(p,r['remove_sha256'],r['remove_bytes']);safe(r['retained_archive']);guard.row(p,r['remove_sha256'],r['remove_bytes'])
 expected=json.loads(Path(r['complete_native_members_reference']).read_bytes())
 if r['kind']=='contained_earlier_portable_payload':
  with tarfile.open(r['retained_archive'],'r:gz') as t:
   for x in expected:
    entry=t.getmember(x['retained_member'])
    if not entry.isfile() or digest(t.extractfile(entry))!=(x['sha256'],x['bytes']):raise ValueError('Exact retained original subset member changed')
 else:
  with guard.complete_archive(p,r['remove_sha256'],r['remove_bytes']) as f:
   if digest(f)!=(r['remove_sha256'],r['remove_bytes']):raise ValueError('Whole complete native retained bytes changed')
  actual=[]
  with guard.complete_archive(p,r['remove_sha256'],r['remove_bytes']) as f:
   with tarfile.open(fileobj=f,mode='r|gz') as t:
    for m in t:
     if m.isfile():
      s,n=digest(t.extractfile(m));actual.append(dict(member=m.name,bytes=n,sha256=s))
  if actual!=expected:raise ValueError('Every complete native member must match')
 if 'retained_flat_archive' in r:safe(r['retained_flat_archive']);checked(r['retained_flat_archive'],r['remove_sha256'],r['remove_bytes'])

def authorization(args):
 if not all([args.authorization,args.authorization_pin,args.user_reply,args.reply_id]):raise ValueError('Actual explicit user reply and whole-byte-pinned authorization required before execution')
 p=Path(args.authorization).resolve()
 if not p.is_relative_to(H):raise ValueError('Actual authorization must be preserved on evidence surface')
 checked(p,args.authorization_pin);a=json.loads(p.read_bytes())
 if (a.get('approved') is not True or a.get('explicit_user_authorization') is not True or a.get('approved_plan_sha256')!=PLAN_PIN or a.get('user_reply')!=args.user_reply or a.get('source_reply_id')!=args.reply_id or a.get('scope_count')!=16 or a.get('scope_bytes')!=450480142):raise ValueError('Actual exact16 scope authorization required')
 return p,a

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--execute',action='store_true');ap.add_argument('--inspect',action='store_true');ap.add_argument('--authorization');ap.add_argument('--authorization-pin');ap.add_argument('--user-reply');ap.add_argument('--reply-id');args=ap.parse_args()
 if args.execute==args.inspect:raise ValueError('Exactly one inspect or execute mode required')
 auth=None
 if args.execute:auth=authorization(args) # Fail closed BEFORE any output or cleanup mutation.
 guard=PreparedResolver();prior_before={}
 for name in ['full118-approved11-cleanup-execution-v1/receipt.json','full118-approved39-cleanup-continuation-v2/receipt.json']:
  prior_before[name]=sha((H/name).read_bytes())
 d=H/('full118-approved16-cleanup-execution-v1' if args.execute else 'full118-consolidated16-preexecution-inspection-v1');d.mkdir(exist_ok=False);(d/'approved-plan.json' if args.execute else d/'inspected-plan.json').write_bytes(PLAN.read_bytes());(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 if args.execute:(d/'authorization.json').write_bytes(auth[0].read_bytes())
 free=shutil.disk_usage(H).free;done=[]
 # Validate the complete exact set before the first removal.
 for p,r in guard.rows.items():verify(guard,p,r)
 for i,(p,r) in enumerate(guard.rows.items()):
  verify(guard,p,r) # Fresh target, retained whole archive and all required members immediately before.
  if args.execute:
   command="Remove-Item -LiteralPath '"+str(p).replace("'","''")+"' -Force -ErrorAction Stop"
   q=subprocess.run(['powershell.exe','-NoProfile','-NonInteractive','-Command',command],capture_output=True)
   (d/f'{i:03d}.stdout').write_bytes(q.stdout);(d/f'{i:03d}.stderr').write_bytes(q.stderr);(d/f'{i:03d}.native-exit.json').write_text(json.dumps(dict(native_exit=q.returncode,path=str(p)))+'\n',encoding='utf-8')
   if q.returncode or p.exists():raise RuntimeError('Exact native single-file removal failed; preserved partial state')
   guard.row(p,r['remove_sha256'],r['remove_bytes']) # Whole retained bytes remain exact after removal.
  done.append(dict(path=str(p),bytes=r['remove_bytes'],sha256=r['remove_sha256'],retained_archive=r['retained_archive'],retained_sha256=r['retained_archive_sha256'],native_exit=0 if args.execute else None,retained_verified_after=True,removed=args.execute))
  (d/'partial-progress.json').write_text(json.dumps(dict(plan_sha256=PLAN_PIN,actual_authorization_present=bool(auth),files=done),indent=2)+'\n',encoding='utf-8')
  print('removed' if args.execute else 'verified',i+1,len(guard.rows),flush=True)
 for name,pin in prior_before.items():
  if sha((H/name).read_bytes())!=pin:raise ValueError('Historical actual cleanup receipt changed')
 j=dict(plan_sha256=PLAN_PIN,complete=True,files_deleted=args.execute,removed_count=len(done) if args.execute else 0,removed_bytes=sum(x['bytes'] for x in done) if args.execute else 0,removed=done if args.execute else [],verified_files=done,retained_originals_unchanged=True,historical_receipt_pins=prior_before,free_before=free,free_after=shutil.disk_usage(H).free,original_gates_unchanged=True,compiler_invoked=False)
 if args.execute:j.update(authorization_sha256=args.authorization_pin,actual_user_reply=args.user_reply,source_reply_id=args.reply_id)
 p=d/('receipt.json' if args.execute else 'inspection.json');p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(result_sha256=sha(p.read_bytes()),execute=args.execute)))
if __name__=='__main__':main()
