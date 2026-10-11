"""Read generated dependency artifact allocation; no file or power changes."""
from datetime import datetime, timezone
import json
from pathlib import Path
from full114_builder02_controller import ROOT
from full114_dedicated_openssh_v2 import Session


def main():
    folder = ROOT / 'generated-capacity-inspections-v2' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True, exist_ok=False)
    (folder / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    guest = """import hashlib,json,os,shutil,stat,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as response:
 assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
assert not (home/'full114-exact-real-complex-operators-repair4-resource02-launch-once.json').exists()
run=home/'cmmsa_a8_output_20261011T060110Z_204d10cd'
assert hashlib.sha256((run/'capture-manifest.json').read_bytes()).hexdigest().upper()=='46D726F1F8D4A1784B5EE4FF6ED6E02AF0EA183AD959A984C525B7F361821A2B'
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip()
 except (FileNotFoundError,PermissionError):continue
 assert name not in ('lean','lake','cp','tar'),(entry,name)
root=run/'.lake/packages';canonical=home/'cmmsa_a8_output_20261007T230522Z_6af6dc24/.lake/packages'
groups={};largest=[]
for parent,dirs,files in os.walk(root,followlinks=False):
 relparent=Path(parent).relative_to(root)
 if not {'.lake','build'}<=set(relparent.parts):continue
 for name in files:
  if name.endswith(('.olean','.olean.private','.olean.server','.ilean')):continue
  p=Path(parent)/name;st=p.lstat()
  if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1 or st.st_size<65536:continue
  rel=p.relative_to(root);dest=canonical/rel
  if not dest.is_file() or dest.stat().st_size!=st.st_size:continue
  suffix=''.join(p.suffixes);g=groups.setdefault(suffix,dict(files=0,logical_bytes=0,allocated_bytes=0))
  g['files']+=1;g['logical_bytes']+=st.st_size;g['allocated_bytes']+=st.st_blocks*512
  largest.append(dict(relative=rel.as_posix(),bytes=st.st_size,allocated_bytes=st.st_blocks*512))
largest=sorted(largest,key=lambda r:r['allocated_bytes'],reverse=True)[:20]
print(json.dumps(dict(groups=groups,largest=largest,disk_available_bytes=shutil.disk_usage(home).free,read_only=True,compiler_invoked=False,content_identity_not_yet_verified=True)))
"""
    scopes = []
    for number in (106, 107, 108, 113):
        root, = [p for p in ROOT.parent.glob('full'+str(number)+'-*') if (p/'launch-once.json').is_file()]
        marker = json.loads((root/'launch-once.json').read_bytes())
        scopes.append(dict(number=number,run=marker['run'],manifest_sha256=__import__('hashlib').sha256((root/'capture-manifest.json').read_bytes()).hexdigest().upper()))
    results = []
    with Session(folder / 'transport') as session:
        for scope in scopes:
            exact = guest.replace('cmmsa_a8_output_20261011T060110Z_204d10cd',scope['run']).replace('46D726F1F8D4A1784B5EE4FF6ED6E02AF0EA183AD959A984C525B7F361821A2B',scope['manifest_sha256'])
            result = json.loads(session.python(exact).read_bytes())
            results.append(dict(**scope,inspection=result))
            (folder / ('inspection-'+str(scope['number'])+'.json')).open('x').write(json.dumps(results[-1],indent=2)+'\n')
            print(json.dumps(dict(number=scope['number'],groups=result['groups'],disk_available_bytes=result['disk_available_bytes'])),flush=True)
    (folder/'inspection.json').open('x').write(json.dumps(dict(scopes=results,read_only=True,compiler_invoked=False),indent=2)+'\n')



if __name__ == '__main__':
    main()
