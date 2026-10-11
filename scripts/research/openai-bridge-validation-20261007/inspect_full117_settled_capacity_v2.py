"""Read-only settled110?114 dependency capacity; original Full117 start retained."""
from datetime import datetime,timezone
import json,shutil
from pathlib import Path
from custody_checks import digest
from full117_builder02_controller import ROOT
from full114_dedicated_openssh_v2 import Session
from start_inspect_full117_owned_capacity_v2 import verify_cleanup_receipt

def main():
    verify_cleanup_receipt();assert shutil.disk_usage(ROOT).free>=1803550720
    here=Path(__file__).resolve().parent
    started=json.loads((ROOT/'start-once.json').read_bytes())
    assert started['vm_id']=='7237681467779354904' and started['source_sha256']==digest(here/'start_inspect_full117_owned_capacity_v2.py')
    original=Path(started['original_start_folder']);native=json.loads((original/'1.lifecycle.json').read_bytes());assert native['native_exit']==0
    for stream in ('stdout','stderr'):assert digest(original/('1.lifecycle.'+stream))==native[stream+'_sha256']
    assert not (ROOT/'launch-once.json').exists()
    folder=ROOT/'capacity-inspections-v2'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');folder.mkdir(parents=True,exist_ok=False)
    (folder/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    scopes = []
    for number in (110, 111, 112, 113, 114):
        roots = [p for p in ROOT.parent.glob('full' + str(number) + '-*') if (p / 'launch-once.json').is_file()]
        assert len(roots) == 1
        marker = json.loads((roots[0] / 'launch-once.json').read_bytes())
        check = Path(marker['preflight'])
        terminal = json.loads((check / 'terminal-custody.json').read_bytes())
        stop = json.loads((check / 'vm-termination.json').read_bytes())
        assert terminal['run'] == stop['run'] == marker['run'] and stop['independent']['status'] == 'TERMINATED'
        scopes.append(dict(number=number, run=marker['run']))
    guest = """import json,os,shutil,stat,urllib.request
from pathlib import Path
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
opener=urllib.request.build_opener(urllib.request.ProxyHandler({}))
req=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with opener.open(req,timeout=10) as r:assert r.headers.get('Metadata-Flavor')=='Google' and r.read().decode()=='7237681467779354904'
assert not (home/'full117-exact-real-complex-operators-repair7-resource02-launch-once.json').exists()
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:name=(p/'comm').read_text().strip()
 except (FileNotFoundError,PermissionError):continue
 assert name not in ('lean','lake','cp','tar'),(str(p),name)
results=[]
for scope in SCOPES:
 root=home/scope['run']/'.lake/packages';groups={}
 for parent,dirs,files in os.walk(root,followlinks=False):
  for name in files:
   p=Path(parent)/name;st=p.lstat();rel=p.relative_to(root);parts=rel.parts
   if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:continue
   if {'.lake','build','lib','lean'}<=set(parts) and name.endswith(('.olean','.olean.private','.olean.server','.ilean')):kind='lean-large' if st.st_size>=65536 else 'lean-small'
   elif ({'.lake','build','ir'}<=set(parts) and name.endswith(('.c','.c.o.export','.setup.json'))) or ({'.lake','build','lib','lean'}<=set(parts) and name.endswith('.ir')) or rel.as_posix() in ('batteries/.lake/build/bin/runLinter','mathlib/.lake/build/bin/cache'):kind='generated'
   else:continue
   g=groups.setdefault(kind,{'files':0,'allocated_bytes':0});g['files']+=1;g['allocated_bytes']+=st.st_blocks*512
 results.append({'number':scope['number'],'run':scope['run'],'groups':groups})
print(json.dumps({'scopes':results,'disk_available_bytes':shutil.disk_usage(home).free,'read_only':True,'compiler_invoked':False}))
""".replace('SCOPES', repr(scopes))
    with Session(folder / 'transport') as session:
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer')
        observed = json.loads(session.python(guest).read_bytes())
        (folder / 'inspection.json').write_text(json.dumps(observed, indent=2) + '\n', encoding='utf-8')
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active')
    print(json.dumps(dict(folder=str(folder), inspection=observed, compiler_invoked=False)), flush=True)

if __name__=='__main__':main()
