"""Stage the exact frozen package after selected-scope audit; no VM start or compiler."""
import base64
from datetime import datetime,timezone
import json
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
    for name in (Path(__file__).name,'full114_dedicated_openssh_v2.py','full115_authorized_cleanup_custody_v1.py'):
        (folder/name).write_bytes((here/name).read_bytes())
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
        compiler_invoked=False,launch_clearance=False,other_vm_modified=False,VM_start_performed=False,
        existing_authenticated_lifecycle=True,transport='existing-trusted-host-key-IAP-OpenSSH',
        full_frozen_remote_preflight_executed=True)
    (folder/'staged.json').open('x').write(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(staging_receipt=str(folder/'staged.json'),prepared=True,compiler_invoked=False)),flush=True)


if __name__=='__main__':main()
