"""Collect verified preflight after environment interruption; no repeated extraction or compile."""
from datetime import datetime,timezone
import json
from pathlib import Path
from custody_checks import digest
from full102_builder02_controller import ROOT,STAGE,VM,VM_ID,NAMES,context,local_gates
from full102_capture_gates import validate_successor


def save(path,value):
    with path.open('x',encoding='utf-8') as stream:json.dump(value,stream,indent=2);stream.write('\n')


def main():
    validate_successor();loaded,runner=context();local_gates(loaded['common'],loaded)
    assert not (ROOT/'launch-once.json').exists()
    prior=ROOT/'existing-staging-resume-controls/20261009T201655177202Z'
    records=json.loads((prior/'commands.json').read_bytes())
    assert len(records)==4 and all(r['native_exit']==0 for r in records)
    stdout=prior/'control/003.stdout'
    assert digest(stdout)==records[3]['stdout_sha256']
    successful=json.loads(stdout.read_bytes())
    folder=ROOT/'existing-preflight-collection-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True);runner.VM=VM
    class Collector(runner.Control):
        def cloud(self,args,**kwargs):
            if args[:3] in (['compute','instances','describe'],['compute','instances','start']):
                assert args[3]==VM
            else:assert args[:2]==['compute','ssh'] and args[2]==VM
            return super().cloud(args,**kwargs)
    control=Collector(folder)
    def describe():
        _,out,_=control.cloud(['compute','instances','describe',VM,'--format=json(name,id,status,zone,machineType,networkInterfaces)'])
        state=json.loads(out)
        assert state['name']==VM and str(state['id'])==VM_ID
        assert state['zone'].rsplit('/',1)[-1]=='us-central1-a' and state['machineType'].rsplit('/',1)[-1]=='e2-highmem-8'
        assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
        return state
    before=describe();control.authenticated=True
    if before['status']=='TERMINATED':
        save(ROOT/'existing-preflight-continuation-boot-once.json',dict(before=before,controls=str(folder),
            successful_original_verifier_stdout_sha256=digest(stdout),compiler_invoked=False))
        control.cloud(['compute','instances','start',VM],timeout=300)
    else:assert before['status']=='RUNNING'
    after=describe();assert after['status']=='RUNNING'
    names=list(NAMES)+['input-archive.tar.gz','capture-manifest.json','resource-binding.json','full102_verify_existing.py']
    expected={n:digest(Path(__file__).with_name(n)) if n in NAMES or n=='full102_verify_existing.py' else digest(ROOT/n) for n in names}
    _,out,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=sha256sum '+' '.join(STAGE+'/'+n for n in names)])
    assert {l.split()[1].rsplit('/',1)[1]:l.split()[0].upper() for l in out.decode().splitlines()}==expected
    _,out,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=cat '+STAGE+'/dependency-preflight.json'])
    preflight=json.loads(out);assert preflight==successful
    binding=json.loads((ROOT/'resource-binding.json').read_bytes())
    assert preflight['auxiliary_inputs_verified']==binding['auxiliary_inputs']
    assert preflight['project_sources_verified']==340 and preflight['warm_objects_verified']==566
    control.cloud(['compute','ssh',VM,'--tunnel-through-iap',
        '--command=set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer'])
    save(folder/'collected-existing-preflight.json',dict(before=before,after=after,preflight=preflight,
         original_verifier_stdout_sha256=digest(stdout),staged_pins=expected,
         original_verifier_repeated=False,extraction_repeated=False,compiler_invoked=False,accepted=False))
    local_gates(loaded['common'],loaded)
    print(json.dumps(dict(collected_existing_preflight=True,receipt=str(folder/'collected-existing-preflight.json'),compiler_invoked=False)))


if __name__=='__main__':main()
