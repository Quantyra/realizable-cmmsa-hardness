"""Stage exact Full118 with one guarded owned-VM start after verified idle stop; no compiler."""
import base64
from datetime import datetime,timezone
import json
import subprocess
import shutil
import time
from finalize_builder02_bootstrap import SDK,FLAGS
from pathlib import Path
from custody_checks import digest
from full118_capture_gates import validate_successor
from full118_builder02_controller import ROOT,STAGE,VM_ID,NAMES,context,local_gates
from full114_dedicated_openssh_v2 import Session


def main():
    verify_cleanup_receipt()
    validate_successor();loaded,_=context();local_gates(loaded['common'],loaded)
    assert not (ROOT/'launch-once.json').exists()
    folder=ROOT/'staging-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True,exist_ok=False)
    here=Path(__file__).resolve().parent
    for name in (Path(__file__).name,'full114_dedicated_openssh_v2.py','full115_authorized_cleanup_custody_v1.py','full115_cumulative_actual_receipts_v1.py','full115_cumulative_cleanup_custody_v2.py'):
        (folder/name).write_bytes((here/name).read_bytes())
    prior_stop=Path('C:\\Users\\dfred\\.quantyra\\builder02\\full117-exact-real-complex-operators-repair7-resource02\\checks\\20261011T231712342988Z\\vm-termination.json')
    assert digest(prior_stop)=='3D451301C7DA2C61075596908128B10C499CB83650067D091410B7F388022826'
    assert digest(here/'full117-native-final-custody-v1/index.json')=='BD6BD71B6EF71EFD6FB6926639BCFA19ADE44CD17DB39D111436EDA04451AC9A'
    assert shutil.disk_usage(ROOT).free >= 1803550720
    stopped=json.loads(prior_stop.read_bytes())
    assert stopped['custody_verified_before_stop'] and stopped['native_terminal']
    assert stopped['run']=='cmmsa_a8_output_20261011T231800Z_f8f19b01'
    assert str(stopped['independent']['id'])==VM_ID and stopped['independent']['status']=='TERMINATED'
    assert not (ROOT/'start-once.json').exists()
    (folder/'prior-native-stop.json').write_bytes(prior_stop.read_bytes())
    for index,args in enumerate((['compute','instances','describe','quantyra-lean-builder-02','--format=json(name,id,status,zone,machineType,networkInterfaces)'],['compute','instances','start','quantyra-lean-builder-02'])):
        argv=[SDK,*args,*FLAGS]
        if index==1:
            (ROOT/'start-once.json').open('x').write(json.dumps(dict(vm_id=VM_ID,argv=argv,source_sha256=digest(Path(__file__)),prior_stop_sha256=digest(prior_stop),original_start_folder=str(folder)),indent=2)+'\n')
        with (folder/(str(index)+'.lifecycle.stdout')).open('xb') as stdout,(folder/(str(index)+'.lifecycle.stderr')).open('xb') as stderr:
            child=subprocess.Popen(argv,stdout=stdout,stderr=stderr,creationflags=subprocess.CREATE_NO_WINDOW)
            record=dict(argv=argv,pid=child.pid)
            (folder/(str(index)+'.lifecycle.json')).write_text(json.dumps(record,indent=2)+'\n')
            while True:
                try:code=child.wait(timeout=30);break
                except subprocess.TimeoutExpired:print(json.dumps(dict(original_lifecycle_process_live=child.pid)),flush=True)
        record.update(native_exit=code,stdout_sha256=digest(folder/(str(index)+'.lifecycle.stdout')),stderr_sha256=digest(folder/(str(index)+'.lifecycle.stderr')))
        (folder/(str(index)+'.lifecycle.json')).write_text(json.dumps(record,indent=2)+'\n')
        assert code==0,'Original lifecycle command failed; preserve without replay'
        if index==0:
            state=json.loads((folder/'0.lifecycle.stdout').read_bytes())
            assert state['name']=='quantyra-lean-builder-02' and str(state['id'])==VM_ID and state['status']=='TERMINATED'
            assert state['zone'].rsplit('/',1)[-1]=='us-central1-a' and state['machineType'].rsplit('/',1)[-1]=='e2-highmem-8'
            assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
    time.sleep(30)
    scopes = []
    for number in (110, 111, 112, 113, 114, 115, 116, 117):
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
assert not (home/'full118-exact-real-complex-operators-repair8-resource02-launch-once.json').exists()
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

def verify_cleanup_receipt():
    here = Path(__file__).resolve().parent
    receipt = here / 'full117-approved20-extracted-cleanup-receipt-v1/receipt.json'
    assert digest(receipt) == '06520876975F04F61497E373F911723B52477A3F985F3494A1D1695D18D8ECC4'
    value = json.loads(receipt.read_bytes())
    assert value['count'] == 20 and value['total_bytes'] == 561073700 and value['all_retained_complete_archives_unchanged']
    assert value['plan_sha256'] == '3D554210BD7BF8285121A3D8C36C765B0CEEDECECF1A4F4ABFE4608D652BF0BF'
    authorization = receipt.parent / 'authorization.json'
    assert digest(authorization) == value['authorization_sha256']
    assert json.loads(authorization.read_bytes())['actual_reply'] == 'Approve these 20 extracted duplicates'
    for row in value['files']:
        assert not Path(row['path']).exists()

if __name__ == '__main__':
    main()
