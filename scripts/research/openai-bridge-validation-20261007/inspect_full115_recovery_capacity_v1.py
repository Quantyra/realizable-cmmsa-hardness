"""Read allocated dependency-object capacity on settled runs; no changes."""
from datetime import datetime, timezone
import json
from pathlib import Path
from full115_builder02_controller import ROOT
from full114_dedicated_openssh_v2 import Session


def main():
    scopes = []
    for n in range(114, 115):
        roots = [p for p in ROOT.parent.glob('full' + str(n) + '-*') if (p / 'launch-once.json').is_file()]
        assert len(roots) == 1, (n, roots)
        marker = json.loads((roots[0] / 'launch-once.json').read_bytes())
        scopes.append(dict(number=n, run=marker['run']))
    folder = ROOT / 'capacity-inspections-v2' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True, exist_ok=False)
    (folder / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    guest = """import json,os,shutil,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as response:
 assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
assert not (home/'full115-exact-real-complex-operators-repair5-resource02-launch-once.json').exists()
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip()
 except (FileNotFoundError,PermissionError):continue
 assert name not in ('lean','lake','cp','tar'),(entry,name)
scopes=SCOPES
results=[]
for scope in scopes:
 root=home/scope['run']/'.lake/packages'
 count=allocated=large_count=large_allocated=0
 for parent,dirs,files in os.walk(root,followlinks=False):
  if not {'.lake','build','lib','lean'}<=set(Path(parent).relative_to(root).parts):continue
  for name in files:
   if not name.endswith(('.olean','.olean.private','.olean.server','.ilean')):continue
   p=Path(parent)/name
   st=p.lstat()
   if not __import__('stat').S_ISREG(st.st_mode) or st.st_nlink!=1:continue
   if 0<st.st_size<65536:count+=1;allocated+=st.st_blocks*512
   elif st.st_size>=65536:large_count+=1;large_allocated+=st.st_blocks*512
 results.append(dict(number=scope['number'],run=scope['run'],small_candidates=count,small_allocated_bytes=allocated,large_candidates=large_count,large_allocated_bytes=large_allocated))
print(json.dumps(dict(scopes=results,disk_available_bytes=shutil.disk_usage(home).free,read_only=True,compiler_invoked=False,content_identity_not_yet_verified=True)))
""".replace('SCOPES', repr(scopes))
    with Session(folder / 'transport') as session:
        result = json.loads(session.python(guest).read_bytes())
        (folder / 'inspection.json').open('x').write(json.dumps(result, indent=2) + '\n')
        print(json.dumps(dict(folder=str(folder), inspection=result)), flush=True)


if __name__ == '__main__':
    main()
