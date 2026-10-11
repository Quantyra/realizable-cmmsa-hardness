"""Stage the exact frozen package after selected-scope audit; no VM start or compiler."""
import base64
from datetime import datetime,timezone
import json
import subprocess
from finalize_builder02_bootstrap import SDK,FLAGS
from pathlib import Path
from custody_checks import digest
from full115_capture_gates import validate_successor
from full115_builder02_controller import ROOT,STAGE,VM_ID,NAMES,context,local_gates
from full114_dedicated_openssh_v2 import Session


def main():
    validate_successor();loaded,_=context();local_gates(loaded['common'],loaded)
    assert not (ROOT/'launch-once.json').exists()
    folder=ROOT/'staging-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True,exist_ok=False)
    here=Path(__file__).resolve().parent
    for name in (Path(__file__).name,'full114_dedicated_openssh_v2.py','full115_authorized_cleanup_custody_v1.py','full115_cumulative_actual_receipts_v1.py','full115_cumulative_cleanup_custody_v2.py'):
        (folder/name).write_bytes((here/name).read_bytes())
    prior_stop=here/'full115-idle-stop-record-20261011T191958661358Z/result.json'
    stopped=json.loads(prior_stop.read_bytes())
    assert stopped['idle_verified_before_stop'] and stopped['independent']['id']==VM_ID and stopped['independent']['status']=='TERMINATED'
    (folder/'prior-idle-stop.json').write_bytes(prior_stop.read_bytes())
    for index,args in enumerate((['compute','instances','describe','quantyra-lean-builder-02','--format=json(name,id,status,zone,machineType,networkInterfaces)'],['compute','instances','start','quantyra-lean-builder-02'])):
        argv=[SDK,*args,*FLAGS]
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
    with Session(folder/'transport') as session:
        before=session.state
        capacity=json.loads(session.python("import json,shutil;print(json.dumps({'free_bytes':shutil.disk_usage('/home/dfredriksen_quantyra_org').free}))").read_bytes())
        assert capacity['free_bytes'] >= 40*1024**3
        (folder/'capacity-admission.json').open('x').write(json.dumps(capacity,indent=2)+'\n')
        session.ssh('set -e; test ! -e '+STAGE+'; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-prepared; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-launch-once.json')
        paths=[ROOT/n for n in ('input-archive.tar.gz','capture-manifest.json','resource-binding.json')]+[here/n for n in NAMES]
        rows=[dict(name=p.name,sha256=digest(p),bytes=p.stat().st_size,base64=base64.b64encode(p.read_bytes()).decode()) for p in paths]
        guest="import base64,hashlib,json\nfrom pathlib import Path\nroot=Path("+repr(STAGE)+")\nassert not root.exists()\nassert not Path("+repr('/home/dfredriksen_quantyra_org/'+ROOT.name+'-prepared')+").exists()\nassert not Path("+repr('/home/dfredriksen_quantyra_org/'+ROOT.name+'-launch-once.json')+").exists()\nrows="+repr(rows)+"\nfor row in rows:\n data=base64.b64decode(row['base64'],validate=True)\n assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256']\nroot.mkdir(exist_ok=False)\nfor row in rows:\n p=root/row['name'];p.open('xb').write(base64.b64decode(row['base64'],validate=True))\n assert hashlib.sha256(p.read_bytes()).hexdigest().upper()==row['sha256']\nprint(json.dumps({row['name']:row['sha256'] for row in rows}))\n"
        uploaded=json.loads(session.python(guest).read_bytes());assert uploaded=={p.name:digest(p) for p in paths}
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer')
        session.ssh('python3 -B '+STAGE+'/full115_verify.py '+STAGE+' '+ROOT.name)
        preflight=json.loads(session.ssh('cat '+STAGE+'/dependency-preflight.json').read_bytes())
        assert preflight['gcp_identity']['id']==VM_ID
        assert preflight['project_sources_verified']==369
    local_gates(loaded['common'],loaded)
    receipt=dict(before=before,dependency_preflight=preflight,uploaded_sha256=uploaded,
        compiler_invoked=False,launch_clearance=False,other_vm_modified=False,VM_start_performed=True,
        existing_authenticated_lifecycle=True,transport='existing-trusted-host-key-IAP-OpenSSH',
        full_frozen_remote_preflight_executed=True)
    (folder/'staged.json').open('x').write(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(staging_receipt=str(folder/'staged.json'),prepared=True,compiler_invoked=False)),flush=True)


if __name__=='__main__':main()
