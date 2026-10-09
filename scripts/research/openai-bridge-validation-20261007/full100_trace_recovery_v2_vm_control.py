"""Exact dedicated02 cache-recovery lease; no Lean/Lake or foreign VM operations."""
from datetime import datetime,timezone
import json
from pathlib import Path
import subprocess
import sys
import time
from full100_consumption_v2_controller import ROOT,VM,VM_ID,ready
from full100_capture_gates import validate_successor
from finalize_builder02_bootstrap import SDK,FLAGS
from custody_checks import digest

def main(action):
    assert action == 'stop', 'Existing recovery boot only; no additional start'
    loaded,runner,binding=ready()
    boot=json.loads((ROOT/'recovery-boot-once.json').read_bytes())
    original=Path(boot['controls']).resolve(strict=True)
    assert original.is_relative_to((ROOT/'recovery-vm-controls').resolve())
    started=json.loads((original/'receipt.json').read_bytes())
    assert started['action']=='start' and started['before']['status']=='TERMINATED' and started['after']['status']=='RUNNING'
    assert str(started['before']['id'])==VM_ID and str(started['after']['id'])==VM_ID
    if (ROOT/'launch-once.json').exists():raise RuntimeError('Trace attempt exists; recovery lease forbidden')
    folder=ROOT/'recovery-vm-controls'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');folder.mkdir(parents=True)
    records=[]
    def call(args,auth=False):
        if not auth:
            if args[:3] in (['compute','instances','describe'],['compute','instances','start'],['compute','instances','stop']):assert args[3]==VM
            elif args[:2]==['compute','ssh']:assert args[2]==VM
            else:raise RuntimeError('Unapproved operation')
        argv=[SDK,*args,*([] if auth else FLAGS)]
        child=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try:out,err=child.communicate(timeout=30);break
            except subprocess.TimeoutExpired:print('Same recovery VM command remains live',child.pid,flush=True)
        i=len(records);(folder/f'{i}.stdout').write_bytes(out);(folder/f'{i}.stderr').write_bytes(err)
        records.append(dict(argv=argv,native_exit=child.returncode));(folder/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
        if child.returncode:raise RuntimeError('Recovery lifecycle failed; inspect original receipt')
        return out
    def state():
        s=json.loads(call(['compute','instances','describe',VM,'--format=json(name,id,status,zone,machineType,networkInterfaces)']))
        assert s['name']==VM and str(s['id'])==VM_ID and s['zone'].rsplit('/',1)[-1]=='us-central1-a' and s['machineType'].rsplit('/',1)[-1]=='e2-highmem-8'
        assert not any(n.get('accessConfigs') for n in s['networkInterfaces'])
        return s
    auth=json.loads(call(['auth','list','--filter=status:ACTIVE','--format=json(account,status)','--account=dfredriksen@quantyra.org','--project=quantyra-lean-cert-20260915','--quiet'],auth=True))
    assert any(r['account']=='dfredriksen@quantyra.org' and r['status']=='ACTIVE' for r in auth)
    before=state()
    if action=='start':
        assert before['status']=='TERMINATED'
        with (ROOT/'recovery-boot-once.json').open('x',encoding='utf-8') as f:json.dump({'controls':str(folder),'before':before,'compiler_invoked':False},f,indent=2)
        call(['compute','instances','start',VM]);after=state();assert after['status']=='RUNNING'
        call(['compute','ssh',VM,'--tunnel-through-iap','--command=set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer'])
    else:
        assert before['status']=='RUNNING'
        assert (ROOT/'recovery-boot-once.json').exists()
        receipts=sorted((ROOT/'cache-repoint-controls').glob('*/operation.json'))
        executed=[]
        for p in receipts:
            r=json.loads(p.read_bytes())
            if r['action']=='execute':
                assert digest(r['local_result'])==r['result_sha256'];v=json.loads(Path(r['local_result']).read_bytes());assert v['content_identity_verified_after_repoint'];executed.append(r)
        assert len(executed)==2
        assert {r['remote_control'] for r in executed}=={'/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v5','/home/dfredriksen_quantyra_org/full100-trace-cache-repoint-v6'}
        assert json.loads(Path(executed[-1]['local_result']).read_bytes())['disk_after_bytes']>=40*1024**3
        raw=call(['compute','ssh',VM,'--tunnel-through-iap','--command=ps -eo pid=,comm='])
        assert not any(line.split()[1] in ('lean','lake','cp','tar','python3') for line in raw.decode().splitlines())
        call(['compute','instances','stop',VM,'--async'])
        while True:
            after=state()
            if after['status']=='TERMINATED':break
            print('Observing same recovery shutdown',after['status'],flush=True);time.sleep(10)
        independent=state();assert independent['status']=='TERMINATED'
    r=dict(action=action,before=before,after=after,authentication=auth,compiler_invoked=False,other_vm_modified=False)
    (folder/'receipt.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r),flush=True)
if __name__=='__main__':main(sys.argv[1])
