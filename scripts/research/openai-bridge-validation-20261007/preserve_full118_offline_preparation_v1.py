"""Preserve exact closed offline preparation wrappers and complete package."""
import hashlib,io,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
R=Path('C:/Users/dfred/.quantyra/builder02/full118-exact-real-complex-operators-repair8-resource02')
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 wrappers=[R.parent/'full117-exact-real-complex-operators-repair7-resource02/research-resume-20261011/20261011T233920953074Z-948210e4e60c',R/'research-resume-20261011/20261011T234159107717Z-87c9f3df2799']
 for w in wrappers:
  j=json.loads((w/'command.json').read_bytes());assert j['native_exit']==0
  for n in ('stdout','stderr'):assert sha((w/n).read_bytes())==j[n+'_sha256']
 result=H/'full118-execution-control-validation-20261011T234200761486Z/result.json';j=json.loads(result.read_bytes());assert all(x['native_exit']==0 for x in j['commands']) and j['full369_full347_seven_stage_capture_verified']
 assert sha((R/'input-archive.tar.gz').read_bytes())=='097DB8FD8BA4922D0BB9698D67CF383D43B4AFBE509EF89E0738A87B82B82C62'
 paths={p for w in [*wrappers,result.parent] for p in w.rglob('*') if p.is_file()}
 paths.update(R/n for n in ('input-archive.tar.gz','capture-manifest.json','resource-binding.json','source-expansion.json'));paths.add(Path(__file__).resolve())
 d=H/'full118-offline-preparation-originals-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 with tarfile.open(d/'originals.tar.gz','x:gz') as t:
  for i,p in enumerate(sorted(paths)):
   assert p.is_file() and not p.is_symlink();b=p.read_bytes();n=f'{i:03d}-{p.name}';ti=tarfile.TarInfo(n);ti.size=len(b);t.addfile(ti,io.BytesIO(b));rows.append(dict(original=str(p),member=n,bytes=len(b),sha256=sha(b)))
 with tarfile.open(d/'originals.tar.gz','r:gz') as t:
  assert len(t.getmembers())==len(rows)
  for r in rows:assert sha(t.extractfile(r['member']).read())==r['sha256'] and sha(Path(r['original']).read_bytes())==r['sha256']
 index=dict(originals=rows,payload_sha256=sha((d/'originals.tar.gz').read_bytes()),offline_validation_result_sha256=sha(result.read_bytes()),handles={'preparation':76054,'validation':22336},terminal_exits={'preparation':0,'validation':0},compiler_invoked=False,cloud_operation=False,accepted=False,launch_clearance=False)
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(files=len(rows),index_sha256=sha((d/'index.json').read_bytes()),validation_sha256=sha(result.read_bytes()))))
if __name__=='__main__':main()
