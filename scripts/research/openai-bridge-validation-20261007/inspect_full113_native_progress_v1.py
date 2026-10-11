"""Read-only Full113 progress; observation cannot replace authoritative native custody."""
from datetime import datetime,timezone
import json
from pathlib import Path
from custody_checks import digest
from full113_builder02_controller import ROOT,VM_ID
from full113_dedicated_openssh_v2 import Session
HERE=Path(__file__).resolve().parent
def main():
    marker=json.loads((ROOT/'launch-once.json').read_bytes())
    assert marker['run']=='cmmsa_a8_output_20261011T060110Z_204d10cd'
    folder=ROOT/'live-native-inspections-v1'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True,exist_ok=False)
    (folder/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    guest="""import json,os,shutil,urllib.request
from pathlib import Path
opener=urllib.request.build_opener(urllib.request.ProxyHandler({}))
request=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with opener.open(request,timeout=10) as response:
 assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
marker=json.loads((home/'full113-exact-real-complex-operators-repair3-resource02-launch-once.json').read_bytes())
assert marker['run']=='cmmsa_a8_output_20261011T060110Z_204d10cd'
root=home/(marker['run']+'_evidence')
records={}
for name in ('active-process.json','begin.native-exit','compile.native-exit','finish.native-exit','aggregate.native-exit','dedicated-worker-terminal.json'):
 p=root/name
 if p.exists():records[name]=p.read_text()
stages=[]
for n in range(7):
 p=root/('stage-'+str(n)+'.command.json')
 if p.exists():stages.append(json.loads(p.read_bytes()))
processes=[]
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip();args=(entry/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError):continue
 if name in ('lean','lake') or (name=='python3' and ('full113_worker.py' in args or marker['run'] in args)):
  processes.append(dict(pid=int(entry.name),name=name,argv=args))
print(json.dumps(dict(run=marker['run'],records=records,stages=stages,live_processes=processes,disk_available_bytes=shutil.disk_usage(home).free,archive_present=(home/(marker['run']+'_evidence.tar.gz')).exists(),read_only=True,compiler_replayed=False,authoritative_terminal_custody=False)))
"""
    with Session(folder/'transport') as session:
        raw=session.python(guest)
        report=json.loads(raw.read_bytes())
        assert report['run']==marker['run']
    (folder/'inspection.json').open('x').write(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(folder=str(folder),run=report['run'],
        completed_stage_exits=[r.get('native_exit') for r in report['stages']],
        live_processes=report['live_processes'],archive_present=report['archive_present'],
        observation_only=True)),flush=True)
if __name__=='__main__':main()

