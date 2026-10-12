"""Read-only exact redundant archive plan; never authorizes or deletes files."""
import hashlib,json,re,shutil,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
BASE=Path('C:/Users/dfred/.quantyra/builder02').resolve(strict=True)
SHORT=Path('C:/a8gcp').resolve(strict=True)
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def digest(p):return sha(p.read_bytes())
def checked(p,base):
 assert p.is_file() and not p.is_symlink();q=p.resolve(strict=True)
 assert q==p.absolute() and q.is_relative_to(base)
 for x in [p,*p.parents]:
  if x.is_relative_to(base):assert not x.is_symlink() and not x.is_junction()
 return q
def main():
 checks={}
 for p in BASE.glob('full*/checks/*/qualified-native/*/remote-evidence/core-sources.tar.gz'):
  number=int(re.match(r'full(\d+)',p.relative_to(BASE).parts[0]).group(1))
  if not 83<=number<=117:continue
  c=BASE.joinpath(*p.relative_to(BASE).parts[:3])
  if (c/'terminal-custody.json').is_file() and (c/'vm-termination.json').is_file():checks[c]=(number,p.parent)
 rows=[]
 for c,(number,evidence) in sorted(checks.items(),key=lambda x:(x[1][0],str(x[0]))):
  terminal_path=checked(c/'terminal-custody.json',BASE);stop_path=checked(c/'vm-termination.json',BASE)
  terminal=json.loads(terminal_path.read_bytes());stop=json.loads(stop_path.read_bytes());run=terminal['run']
  assert run==stop['run']==evidence.parent.name
  assert terminal['terminal']['native_terminal'] and stop['custody_verified_before_stop']
  assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
  custody=terminal['custody'];retained=checked(Path(custody['repository_path']),BASE)
  assert retained.is_relative_to(c) and retained.stat().st_size==custody['bytes'] and digest(retained)==custody['remote_sha256']
  selected=[('extracted_member',checked(evidence/'core-sources.tar.gz',BASE),'core-sources.tar.gz')]
  if 110<=number<=117:
   selected.append(('extracted_member',checked(evidence/'package-sources.tar.gz',BASE),'package-sources.tar.gz'))
  if 115<=number<=117:
   p=checked(Path(custody['short_path']),SHORT);assert p!=retained
   selected.append(('short_complete_native_duplicate',p,None))
  with tarfile.open(retained,'r:gz') as t:
   members=t.getmembers();assert members and all(m.isfile() for m in members) and len(members)==len({m.name for m in members})
   owner=json.loads(t.extractfile('dedicated-worker-terminal.json').read());assert owner['run']==run and str(owner['host']['id'])=='7237681467779354904'
   for kind,p,member in selected:
    raw=p.read_bytes();pin=sha(raw)
    if member:assert t.extractfile(member).read()==raw
    else:assert len(raw)==custody['bytes'] and pin==custody['remote_sha256']
    assert digest(p)==pin
    rows.append(dict(kind=kind,number=number,run=run,remove=str(p),bytes=len(raw),sha256=pin,retain_complete_native_archive=str(retained),retained_archive_bytes=retained.stat().st_size,retained_archive_sha256=custody['remote_sha256'],retained_member=member,retained_member_bytes=len(raw) if member else None,retained_member_sha256=pin if member else None,terminal_receipt=str(terminal_path),terminal_receipt_sha256=digest(terminal_path),independent_stop=str(stop_path),independent_stop_sha256=digest(stop_path),entire_retained_archive_and_member_identity_verified=True,native_archive_members=len(members)))
  assert digest(retained)==custody['remote_sha256']
 total=sum(r['bytes'] for r in rows);assert len({r['remove'] for r in rows})==len(rows) and total>=300*1024**2
 d=H/'full118-settled-duplicate-archive-cleanup-plan-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 plan=dict(files=rows,count=len(rows),total_bytes=total,free_bytes=shutil.disk_usage(BASE).free,required_local_bytes=1803550720,explicit_authorization_required=True,authorization_received=False,files_deleted=False,scope='Exact listed settled extracted core archives, Full110–117 extracted package archives, and Full115–117 short complete duplicate archives.',retention='Every complete repository native archive stays unchanged and contains exact extracted member bytes. Three short duplicates require a disjoint exact authorized one-copy adapter after actual approval; historical two-copy receipts remain unchanged.',unique_data_deleted=False,live_full118_input_and_source_excluded=True,compiler_invoked=False,cloud_operation=False,new_resources=False,admission_guards_unchanged=True,execution_requires_fresh_containment_hashes_retained_member_checks_and_exact_authorization_receipt=True)
 (d/'plan.json').write_bytes((json.dumps(plan,indent=2)+'\n').encode());print(json.dumps(dict(path=str(d/'plan.json'),sha256=digest(d/'plan.json'),count=len(rows),total_bytes=total,short_duplicate_count=sum(r['kind']=='short_complete_native_duplicate' for r in rows))))
if __name__=='__main__':main()
