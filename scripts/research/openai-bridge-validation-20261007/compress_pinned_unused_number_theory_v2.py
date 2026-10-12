from pathlib import Path
import hashlib,json,subprocess,shutil,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full119_retired_plans_journals_ntfs_v1 import allocation
ROOT=Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008');SCOPES=[ROOT/'lean/OAI/NumberTheory']
REV='adc7f1241b42e322a6451854ab7e4b4c146bf78a';OUT=H/'pinned-unused-number-theory-ntfs-compression-v2'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
class GitBytes:
 def __init__(self):self.p=subprocess.Popen(['git','-C',str(ROOT),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 def read(self,path):
  self.p.stdin.write((REV+':'+path+'\n').encode());self.p.stdin.flush();header=self.p.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob';size=int(header[2]);b=self.p.stdout.read(size);assert len(b)==size and self.p.stdout.read(1)==b'\n';return header[0],b
 def close(self):
  self.p.stdin.close();assert self.p.wait()==0;assert not self.p.stderr.read()
def main():
 OUT.mkdir(exist_ok=False);(OUT/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');(OUT/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 native=Path('C:/Users/dfred/.quantyra/builder02/full119-exact-real-complex-operators-repair9-resource02/capture-manifest.json');nb=native.read_bytes();joint=(H/'joint-codec-environment-source-plan-v1/manifest.json').read_bytes();assert all(name.encode() not in nb and name.encode() not in joint for name in ['OAI/NumberTheory','OAI.NumberTheory'])
 rows=[];total=0;git=GitBytes();done=set()
 for name in ['pinned-unused-ramsey-certificate-ntfs-compression-v1','pinned-unused-planar-certificate-ntfs-compression-v1','pinned-unused-mutually-unbiased-ntfs-compression-v1']:
  done.update(r['path'] for r in json.loads((H/name/'receipt.json').read_bytes())['files'])
 for p in sorted([p for scope in SCOPES for p in scope.rglob('*.lean')],key=lambda p:(-p.stat().st_size,str(p))):
  size=p.stat().st_size
  if str(p) in done or p.stat().st_file_attributes&0x800:continue
  if total+size>96*1024**2:continue
  assert p.is_file() and not p.is_symlink() and not(p.stat().st_file_attributes&0x400);assert any(p.resolve().is_relative_to(scope.resolve()) for scope in SCOPES)
  a=allocation(p)
  if a<size:continue
  rel=p.relative_to(ROOT).as_posix();b=p.read_bytes();b.decode('utf8');oid,raw=git.read(rel);assert raw==b
  rows.append(dict(path=str(p),git_path=rel,git_blob=oid,bytes=len(b),sha256=sha(b),allocation_before=a));total+=size
 git.close();assert rows and total<=96*1024**2
 plan=dict(revision=REV,scopes=[str(scope) for scope in SCOPES],files=rows,raw_git_bytes_verified=True,logical_bytes=total,authorization='Root NEW explicit own-cache NumberTheory-only positive list authorization at most128MiB; this concrete plan caps96MiB largest-first for control/custody headroom, raw pinned Git and bytes unchanged; no deletion/config/content change/guard exception',active_native_manifest_sha256=sha(nb),joint_source_manifest_sha256=sha(joint),excluded_active_and_joint_source_inputs=True,original_portable_failure_wrapper='20261012T075804940697Z-cbe136fac8a0',prior_compressed_paths_excluded=True,full120_failed_preparation_record='full120-offline-preparation-v2-record-v1')
 (OUT/'frozen-positive-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf8');before=shutil.disk_usage(H).free;results=[]
 for start in range(0,len(rows),40):
  batch=rows[start:start+40]
  for r in batch:
   b=Path(r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];b.decode('utf8')
  argv=['compact.exe','/C','/Q','/I']+[r['path'] for r in batch]
  with (OUT/f'{start:04d}.stdout').open('xb') as out,(OUT/f'{start:04d}.stderr').open('xb') as err:code=subprocess.run(argv,stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW).returncode
  assert code==0
  for r in batch:
   p=Path(r['path']);b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];b.decode('utf8');results.append(dict(**r,allocation_after=allocation(p),native_exit=code,batch=start,content_unchanged=True,utf8_readable=True))
 git=GitBytes()
 for r in results:
  oid,b=git.read(r['git_path']);assert oid==r['git_blob'] and len(b)==r['bytes'] and sha(b)==r['sha256'] and Path(r['path']).read_bytes()==b
 git.close();report=dict(files=results,free_before=before,free_after=shutil.disk_usage(H).free,reclaimed=sum(r['allocation_before']-r['allocation_after'] for r in results),raw_git_identity_verified_before_and_after=True,source_contents_changed=False,deleted=False,compiler_invoked=False,authorization=plan['authorization'],original_portable_failure_wrapper=plan['original_portable_failure_wrapper'])
 (OUT/'receipt.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(files=len(rows),logical_bytes=total,free_after=report['free_after'],reclaimed=report['reclaimed'],receipt_sha256=sha((OUT/'receipt.json').read_bytes()))))
if __name__=='__main__':main()
