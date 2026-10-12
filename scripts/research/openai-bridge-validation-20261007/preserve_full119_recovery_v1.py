import gzip,hashlib,io,json,sys,tarfile
from pathlib import Path
from custody_checks import digest
from run_full119_cache_recovery_v1 import ROOT,RECOVERY,DERIVATION,verified_plans,scopes
H=Path(__file__).resolve().parent
def main(phase):
 assert phase in ('plans','complete');summaries=verified_plans()
 if phase=='complete':
  from audit_full119_cache_recovery_v1 import validate_local_audit
  validate_local_audit()
 else:assert not (RECOVERY/'execution-request-once.json').exists()
 paths={Path(__file__).resolve(),DERIVATION,H/'run_full119_cache_recovery_v1.py'}
 paths.update(H/s['helper'] for s in scopes())
 for folder in [RECOVERY,ROOT/'earlier-settled-capacity-inspection-v1',ROOT/'earlier-settled-capacity-inspection-v2',ROOT/'staging-controls']:
  paths.update(p for p in folder.rglob('*') if p.is_file())
 for folder in (ROOT/'research-resume-20261011').iterdir():
  p=folder/'command.json'
  if not p.is_file():continue
  v=json.loads(p.read_bytes())
  if 'native_exit' not in v and any(Path(str(x)).name=='preserve_full119_recovery_v1.py' for x in v['argv']):continue
  assert 'native_exit' in v,('Original controller still live',folder)
  for n in ('stdout','stderr'):assert digest(folder/n)==v[n+'_sha256']
  paths.update(q for q in folder.rglob('*') if q.is_file())
 d=H/('full119-recovery-'+phase+'-record-v1');d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');archive=d/'complete-originals.tar.gz';rows=[]
 with archive.open('xb') as raw:
  with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as z:
   with tarfile.open(fileobj=z,mode='w') as t:
    for i,p in enumerate(sorted(paths)):
     b=p.read_bytes();pin=hashlib.sha256(b).hexdigest().upper();n=f'{i:04d}-'+p.name;info=tarfile.TarInfo(n);info.size=len(b);info.mode=0o644;t.addfile(info,io.BytesIO(b));rows.append(dict(original=str(p),member=n,bytes=len(b),sha256=pin));assert digest(p)==pin
 with tarfile.open(archive,'r:gz') as t:
  for r in rows:
   b=t.extractfile(r['member']).read();assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest().upper()==r['sha256'] and digest(Path(r['original']))==r['sha256']
 j=dict(files=rows,scopes=summaries,all_selected_plans_verified=True,execution_included=phase=='complete',payload=dict(file=archive.name,bytes=archive.stat().st_size,sha256=digest(archive)),all_members_roundtrip_verified=True,files_deleted=False,compiler_invoked=False,accepted=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(index=str(d/'index.json'),sha256=digest(d/'index.json'),payload_bytes=archive.stat().st_size)))
if __name__=='__main__':main(sys.argv[1])
