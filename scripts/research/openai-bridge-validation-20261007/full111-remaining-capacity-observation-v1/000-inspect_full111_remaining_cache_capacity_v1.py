"""Read remaining allocated duplicate candidates; no planner or execution replay."""
from datetime import datetime,timezone
import json
from pathlib import Path
from full111_builder02_controller import ROOT
from full112_dedicated_openssh_v1 import Session


def main():
    scopes=[]
    for n in (109,110,111):
        root=ROOT if n==111 else next(ROOT.parent.glob('full'+str(n)+'-*'))
        marker=json.loads((root/'launch-once.json').read_bytes())
        scopes.append(dict(number=n,run=marker['run']))
    folder=ROOT/'remaining-capacity-inspections-v1'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True,exist_ok=False)
    (folder/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    guest="""import json,os,shutil,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as response:
 assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
assert not (home/'full112-exact-real-complex-operators-repair2-resource02-launch-once.json').exists()
scopes=SCOPES
results=[]
for scope in scopes:
 root=home/scope['run']/'.lake/packages'
 count=0;allocated=0;large_count=0;large_allocated=0
 for p in root.rglob('*'):
  if p.is_symlink() or not p.is_file():continue
  rel=p.relative_to(root)
  if not p.name.endswith(('.olean','.olean.private','.olean.server','.ilean')):continue
  if not {'.lake','build','lib','lean'}<=set(rel.parts):continue
  st=p.stat()
  if st.st_nlink!=1:continue
  if 0<st.st_size<65536:count+=1;allocated+=st.st_blocks*512
  elif st.st_size>=65536:large_count+=1;large_allocated+=st.st_blocks*512
 results.append(dict(number=scope['number'],run=scope['run'],small_candidates=count,small_allocated_bytes=allocated,
                     large_candidates=large_count,large_allocated_bytes=large_allocated))
print(json.dumps(dict(scopes=results,disk_available_bytes=shutil.disk_usage(home).free,
 read_only=True,compiler_invoked=False,content_identity_not_yet_verified=True)))
""".replace('SCOPES',repr(scopes))
    with Session(folder/'transport') as session:
        raw=session.python(guest);result=json.loads(raw.read_bytes())
        (folder/'inspection.json').open('x').write(json.dumps(result,indent=2)+'\n')
        print(json.dumps(dict(folder=str(folder),inspection=result)),flush=True)


if __name__=='__main__':main()
