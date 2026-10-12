"""Stage exact Full119 after preserved lossless recovery; retain original start; no compiler."""
import base64
from datetime import datetime,timezone
import json
import subprocess
import shutil
import time
from finalize_builder02_bootstrap import SDK,FLAGS
from pathlib import Path
from custody_checks import digest
from full119_capture_gates import validate_successor
from full119_builder02_controller import ROOT,STAGE,VM_ID,NAMES,context,local_gates
from full114_dedicated_openssh_v2 import Session


def main():
    validate_successor();loaded,_=context();local_gates(loaded['common'],loaded)
    assert not (ROOT/'launch-once.json').exists()
    folder=ROOT/'staging-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True,exist_ok=False)
    here=Path(__file__).resolve().parent
    for name in (Path(__file__).name,'full114_dedicated_openssh_v2.py','full115_authorized_cleanup_custody_v1.py','full115_cumulative_actual_receipts_v1.py','full115_cumulative_cleanup_custody_v2.py','full119_authorized16_nested_custody_v3.py','full119_pending16_nested_custody_v2.py','full118_consolidated_preservation_resolver_v1.py'):
        (folder/name).write_bytes((here/name).read_bytes())
    prior_stop=Path('C:\\Users\\dfred\\.quantyra\\builder02\\full118-exact-real-complex-operators-repair8-resource02\\checks\\20261012T023543679265Z\\vm-termination.json')
    assert digest(prior_stop)=='85D67B53B8CFA892E2982F6D88D6E7F0665029068253E9D1AFF59AE047A83A68'
    assert digest(here/'full118-native-final-custody-v1/index.json')=='F9371ACD70F164BB808EEBF20D339EBEFBF1C4AE2EF1E9F48DD6BCA99BFFC25A'
    assert shutil.disk_usage(ROOT).free >= 1803550720
    stopped=json.loads(prior_stop.read_bytes())
    assert stopped['custody_verified_before_stop'] and stopped['native_terminal']
    assert stopped['run']=='cmmsa_a8_output_20261012T023620Z_8ea3737a'
    assert str(stopped['independent']['id'])==VM_ID and stopped['independent']['status']=='TERMINATED'
    import full119_authorized16_nested_custody_v3 as actual
    actual.configured_guard().documents()
    started=json.loads((ROOT/'start-once.json').read_bytes())
    assert started['vm_id']==VM_ID and started['source_sha256']==digest(here/'start_inspect_full119_owned_capacity_v1.py')
    assert started['prior_stop_sha256']==digest(prior_stop)
    original=Path(started['original_start_folder']);life=json.loads((original/'1.lifecycle.json').read_bytes())
    assert life['native_exit']==0
    for stream in ('stdout','stderr'):
        assert digest(original/('1.lifecycle.'+stream))==life[stream+'_sha256']
    inspection=json.loads((original/'inspection.json').read_bytes())
    assert inspection['read_only'] and not inspection['compiler_invoked']
    assert inspection['disk_available_bytes'] < 40*1024**3, 'Original failed capacity guard identity changed'
    from audit_full119_cache_recovery_v1 import validate_local_audit, AUDIT
    report=validate_local_audit()
    custody=here/'full119-recovery-complete-record-v1/index.json';preserved=json.loads(custody.read_bytes())
    assert preserved['all_selected_plans_verified'] and preserved['execution_included'] and preserved['all_members_roundtrip_verified']
    payload=custody.parent/preserved['payload']['file'];assert digest(payload)==preserved['payload']['sha256'] and payload.stat().st_size==preserved['payload']['bytes']
    audit_path=AUDIT/'audit.json';matches=[r for r in preserved['files'] if r['original']==str(audit_path)];assert len(matches)==1
    audit_row=matches[0];assert digest(audit_path)==audit_row['sha256']
    import tarfile
    with tarfile.open(payload,'r:gz') as archive:assert archive.extractfile(audit_row['member']).read()==audit_path.read_bytes()
    assert report['disk_available_bytes']>=40*1024**3 and report['state']['status']=='RUNNING' and str(report['state']['id'])==VM_ID
    (folder/'verified-recovery-audit.json').write_bytes(audit_path.read_bytes())
    (folder/'verified-recovery-custody-index.json').write_bytes(custody.read_bytes())
    (ROOT/'recovery-stage-request-once.json').open('x').write(json.dumps(dict(source_sha256=digest(Path(__file__)),actual16_receipt_sha256=digest(here/'full118-approved16-cleanup-execution-v1/receipt.json'),original_start_folder=str(original),inspection_sha256=digest(original/'inspection.json')))+'\n')
    (folder/'prior-native-stop.json').write_bytes(prior_stop.read_bytes())
    with Session(folder/'transport') as session:
        before=session.state
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; systemctl is-active quantyra-idle-shutdown.timer')
        capacity=json.loads(session.python("import json,shutil;print(json.dumps({'free_bytes':shutil.disk_usage('/home/dfredriksen_quantyra_org').free}))").read_bytes())
        assert capacity['free_bytes'] >= 40*1024**3
        (folder/'capacity-admission.json').open('x').write(json.dumps(capacity,indent=2)+'\n')
        session.ssh('set -e; test ! -e '+STAGE+'; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-prepared; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-launch-once.json')
        paths=[ROOT/n for n in ('input-archive.tar.gz','capture-manifest.json','resource-binding.json')]+[here/n for n in NAMES]
        rows=[dict(name=p.name,sha256=digest(p),bytes=p.stat().st_size,base64=base64.b64encode(p.read_bytes()).decode()) for p in paths]
        guest="import base64,hashlib,json\nfrom pathlib import Path\nroot=Path("+repr(STAGE)+")\nassert not root.exists()\nassert not Path("+repr('/home/dfredriksen_quantyra_org/'+ROOT.name+'-prepared')+").exists()\nassert not Path("+repr('/home/dfredriksen_quantyra_org/'+ROOT.name+'-launch-once.json')+").exists()\nrows="+repr(rows)+"\nfor row in rows:\n data=base64.b64decode(row['base64'],validate=True)\n assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256']\nroot.mkdir(exist_ok=False)\nfor row in rows:\n p=root/row['name'];p.open('xb').write(base64.b64decode(row['base64'],validate=True))\n assert hashlib.sha256(p.read_bytes()).hexdigest().upper()==row['sha256']\nprint(json.dumps({row['name']:row['sha256'] for row in rows}))\n"
        uploaded=json.loads(session.python(guest).read_bytes());assert uploaded=={p.name:digest(p) for p in paths}
        session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; systemctl is-active quantyra-idle-shutdown.timer')
        session.ssh('python3 -B '+STAGE+'/full119_verify.py '+STAGE+' '+ROOT.name)
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
