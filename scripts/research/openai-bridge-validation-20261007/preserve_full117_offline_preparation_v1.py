"""Lossless local custody of offline preparation and pending cleanup plan."""
import hashlib,io,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
R=Path('C:/Users/dfred/.quantyra/builder02/full116-exact-real-complex-operators-repair6-resource02/research-resume-20261011')
S=Path('C:/Users/dfred/.quantyra/builder02/full117-exact-real-complex-operators-repair7-resource02')
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 roots=[R/n for n in ['20261011T215417352586Z-116a2dc9777d','20261011T215949457138Z-06eef0a8ce30','20261011T215958125547Z-6a88ddc513a5','20261011T220140249767Z-f1ca527ae09f']]
 paths=[p for root in roots for p in sorted(root.rglob('*')) if p.is_file()]
 paths += [S/n for n in ['input-archive.tar.gz','capture-manifest.json','resource-binding.json','source-expansion.json']]
 result=H/'full117-execution-control-validation-20261011T220141729530Z/result.json';j=json.loads(result.read_bytes());assert all(c['native_exit']==0 for c in j['commands']) and j['full369_full347_seven_stage_capture_verified']
 assert sha((S/'input-archive.tar.gz').read_bytes())=='41BB9B0B971C39A85B49DB5D4FCC98445535242DBA0C13A4BEC5696124EDF3C4'
 d=H/'full117-offline-preparation-originals-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 with tarfile.open(d/'originals.tar.gz','w:gz') as t:
  for i,p in enumerate(paths):
   assert not p.is_symlink();b=p.read_bytes();n=f'{i:03d}-{p.name}';ti=tarfile.TarInfo(n);ti.size=len(b);t.addfile(ti,io.BytesIO(b));rows.append(dict(original=str(p),member=n,bytes=len(b),sha256=sha(b)))
 with tarfile.open(d/'originals.tar.gz','r:gz') as t:
  assert len(t.getmembers())==len(rows)
  for r in rows:assert sha(t.extractfile(r['member']).read())==r['sha256']
 index=dict(originals=rows,payload_sha256=sha((d/'originals.tar.gz').read_bytes()),offline_validation_result_sha256=sha(result.read_bytes()),handles={'cleanup_plan':76652,'derivation':7816,'preparation':8865,'validation':71477},terminal_exits={'cleanup_plan':0,'derivation':0,'preparation':0,'validation':0},compiler_invoked=False,cloud_operation=False,accepted=False,cleanup_authorization_pending=True,launch_clearance=False)
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(files=len(rows),index_sha256=sha((d/'index.json').read_bytes()),validation_sha256=sha(result.read_bytes()))))
if __name__=='__main__':main()
