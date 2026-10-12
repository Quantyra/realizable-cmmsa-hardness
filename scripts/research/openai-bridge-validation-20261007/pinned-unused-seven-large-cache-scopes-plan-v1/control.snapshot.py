from pathlib import Path
import sys,json,hashlib,subprocess
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
from compress_full119_retired_plans_journals_ntfs_v1 import allocation
ROOT=Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008');REV='adc7f1241b42e322a6451854ab7e4b4c146bf78a'
NAMES=['Combinatorics/Ramsey','LinearAlgebra/MatrixFields','Geometry/EinsteinFour','Combinatorics/HoneycombChords','Analysis/Triangular','GameTheory/SnakyConditional','RepresentationTheory/UniversalSquare']
OUT=H/'pinned-unused-seven-large-cache-scopes-plan-v1'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 OUT.mkdir(exist_ok=False);(OUT/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');(OUT/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 pins={}
 for p in [Path('C:/Users/dfred/.quantyra/builder02/full120-exact-real-complex-operators-warning-cleanup-resource02/capture-manifest.json'),H/'joint-codec-minimal-source-closure-v3/manifest.json',H/'joint-codec-minimal-source-custody-v3/index.json',H/'tm2-cobham-transfer-capture-20261012-v4/index.json',H/'numeric-numbered-occurrence-producer-capture-v17/index.json']:
  pins[str(p)]=sha(p.read_bytes())
 done=set()
 for p in H.glob('*ntfs-compression*/receipt.json'):
  obj=json.loads(p.read_bytes())
  for r in obj.get('files',[]):
   if 'path' in r:done.add(str(Path(r['path']).resolve()).casefold())
 candidates=[]
 for n in NAMES:
  scope=ROOT/'lean/OAI'/n;assert scope.resolve().is_relative_to((ROOT/'lean/OAI').resolve())
  for p in scope.rglob('*.lean'):
   st=p.stat()
   if st.st_size<65536 or st.st_file_attributes&(0x400|0x800) or str(p.resolve()).casefold() in done:continue
   assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(scope.resolve());assert 'Computability' not in p.parts
   candidates.append((p,n))
 candidates.sort(key=lambda x:(-x[0].stat().st_size,str(x[0])))
 tree=subprocess.check_output(['git','-C',str(ROOT),'ls-tree','-r',REV,'--','lean/OAI']);ids={}
 for line in tree.splitlines():
  meta,path=line.split(b'\t',1);mode,kind,oid=meta.split();ids[path.decode()]=(mode.decode(),oid.decode())
 proc=subprocess.Popen(['git','-C',str(ROOT),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 rows=[];total=0
 for p,n in candidates:
  b=p.read_bytes();assert not b.startswith(b'\xef\xbb\xbf');b.decode('utf8');rel=p.relative_to(ROOT).as_posix();mode,oid=ids[rel];assert mode=='100644'
  proc.stdin.write((oid+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().split();size=int(header[2]);raw=proc.stdout.read(size);assert proc.stdout.read(1)==b'\n' and raw==b
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==oid
  assert total+len(b)<=80*1024**2
  rows.append(dict(path=str(p),scope=n,git_path=rel,git_blob=oid,bytes=len(b),sha256=sha(b),allocation_before=allocation(p)));total+=len(b)
 proc.stdin.close();assert proc.wait()==0
 report=dict(revision=REV,scopes=NAMES,files=rows,logical_bytes=total,allocation_before=sum(r['allocation_before'] for r in rows),active_input_pins=pins,whole_computability_excluded=True,prior_compression_paths_excluded=True,raw_git_bytes_verified=True,compiler_invoked=False,mutation_executed=False,authority='Root candidate preparation only; await exact scope review before execution',expected_reclaim_unverified=True)
 (OUT/'frozen-positive-plan.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
 print(json.dumps(dict(files=len(rows),logical_bytes=total,allocation_before=report['allocation_before'],plan_sha256=sha((OUT/'frozen-positive-plan.json').read_bytes()),scopes={n:dict(files=sum(r['scope']==n for r in rows),bytes=sum(r['bytes'] for r in rows if r['scope']==n),allocated=sum(r['allocation_before'] for r in rows if r['scope']==n)) for n in NAMES})))
if __name__=='__main__':main()
