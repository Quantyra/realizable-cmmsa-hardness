"""Recheck existing prepared source after verified recovery, no second start or compiler."""
from datetime import datetime,timezone
import json
from pathlib import Path
from custody_checks import digest
from full105_builder02_controller import ROOT,STAGE,VM,VM_ID,NAMES,context,local_gates
from full105_capture_gates import validate_successor


def main():
    validate_successor();loaded,runner=context();local_gates(loaded['common'],loaded)
    assert not (ROOT/'launch-once.json').exists()
    prior=sorted((ROOT/'staging-controls').glob('*/commands.json'))[-1]
    records=json.loads(prior.read_bytes())
    assert records[-1]['native_exit']==1 and 'full105_verify.py' in ' '.join(records[-1]['argv'])
    assert 'fresh memory/storage gate failed' in (prior.parent/'7.stderr').read_text()
    applied=[]
    for p in (ROOT/'cache-repoint-controls').glob('*/operation.json'):
        operation=json.loads(p.read_bytes())
        if operation['action']=='execute':
            receipt=json.loads(Path(operation['local_result']).read_bytes())
            assert digest(operation['local_result'])==operation['result_sha256']
            assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
            applied.append(operation['remote_control'])
    assert set(applied)=={'/home/dfredriksen_quantyra_org/full105-storage-cache-repoint-v3','/home/dfredriksen_quantyra_org/full105-storage-cache-repoint-v4'}
    from audit_full105_storage_recovery_v3_v4 import receipt_review
    receipt_review(3);receipt_review(4)
    folder=ROOT/'existing-staging-resume-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True);runner.VM=VM;control=runner.Control(folder)
    _,out,_=control.cloud(['compute','instances','describe',VM,'--format=json(name,id,status,zone,networkInterfaces)'])
    state=json.loads(out)
    assert state['name']==VM and str(state['id'])==VM_ID and state['status']=='RUNNING'
    assert state['zone'].rsplit('/',1)[-1]=='us-central1-a'
    assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
    control.authenticated=True
    source=Path(__file__).with_name('full105_verify_existing.py')
    control.cloud(['compute','scp',str(source),VM+':'+STAGE+'/', '--tunnel-through-iap'])
    names=list(NAMES)+['input-archive.tar.gz','capture-manifest.json','resource-binding.json',source.name]
    expected={name:digest(Path(__file__).with_name(name)) if name in NAMES or name==source.name else digest(ROOT/name) for name in names}
    _,out,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=sha256sum '+' '.join(STAGE+'/'+name for name in names)])
    assert {l.split()[1].rsplit('/',1)[1]:l.split()[0].upper() for l in out.decode().splitlines()}==expected
    control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=python3 -B '+STAGE+'/'+source.name+' '+STAGE+' '+ROOT.name],timeout=600)
    _,out,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=cat '+STAGE+'/dependency-preflight.json'])
    receipt=json.loads(out)
    assert receipt['project_sources_verified']==344 and receipt['warm_objects_verified']==566
    assert receipt['disk_available_bytes']>=40*1024**3 and receipt['available_memory_bytes']>=48*1024**3
    assert receipt['auxiliary_inputs_verified']==json.loads((ROOT/'resource-binding.json').read_bytes())['auxiliary_inputs']
    (folder/'verified-existing-stage.json').write_text(json.dumps(dict(preflight=receipt,control_sha256=digest(source),
        prior_failure=str(prior),recovery_scopes=applied,second_start=False,compiler_invoked=False,accepted=False),indent=2)+'\n')
    local_gates(loaded['common'],loaded)
    print(json.dumps(dict(existing_stage_verified=True,receipt=str(folder/'verified-existing-stage.json'),compiler_invoked=False)))


if __name__=='__main__':main()
