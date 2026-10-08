"""Finalize authorized dedicated VM bootstrap with exact-target native receipts."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

SDK='C:/Users/dfred/AppData/Local/Google/Cloud SDK/google-cloud-sdk/bin/gcloud.cmd'
VM='quantyra-lean-builder-02'
ID='7237681467779354904'
FLAGS=['--account=dfredriksen@quantyra.org','--project=quantyra-lean-cert-20260915','--zone=us-central1-a','--quiet']
STAGE='/home/dfredriksen_quantyra_org/full83-builder02-bootstrap-v2'
ROOT=Path('C:/Users/dfred/.quantyra/builder02/full83-resource02')

def main():
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    receipt=ROOT/'bootstrap-controls'/stamp; receipt.mkdir(parents=True)
    records=[]
    def cloud(args):
        if args[:3] in (['compute','instances','describe'],['compute','instances','delete-access-config']):
            if args[3] != VM: raise RuntimeError('Foreign VM target')
        elif args[:2] == ['compute','ssh']:
            if args[2] != VM: raise RuntimeError('Foreign SSH target')
        else: raise RuntimeError('Unapproved bootstrap operation')
        command=[SDK,*args,*FLAGS]
        index=len(records)
        process=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try: out,err=process.communicate(timeout=30); break
            except subprocess.TimeoutExpired: print('Same bootstrap command remains active',process.pid,flush=True)
        (receipt/(str(index)+'.stdout')).write_bytes(out); (receipt/(str(index)+'.stderr')).write_bytes(err)
        records.append(dict(argv=command,native_exit=process.returncode,utc=datetime.now(timezone.utc).isoformat()))
        (receipt/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
        if process.returncode: raise RuntimeError('Bootstrap SDK operation failed; retain existing receipt '+str(receipt))
        return out
    def describe():
        state=json.loads(cloud(['compute','instances','describe',VM,'--format=json(name,id,status,zone,networkInterfaces)']))
        if state['name'] != VM or str(state['id']) != ID or state['status'] != 'RUNNING' or state['zone'].rsplit('/',1)[-1] != 'us-central1-a':
            raise RuntimeError('Unexpected dedicated VM identity/state')
        return state
    before=describe()
    preflight=json.loads(cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=cat '+STAGE+'/dependency-preflight.json']))
    manifest=json.loads((ROOT/'capture-manifest.json').read_bytes())
    if preflight['gcp_identity']['id'] != ID or preflight['compiler_sha256'] != manifest['cache_provenance']['compiler']['sha256']:
        raise RuntimeError('Dependency identity mismatch')
    for field,category in [('package_sources_verified','package_sources'),('core_sources_verified','core_sources'),('warm_objects_verified','objects')]:
        if preflight[field] != len(manifest['cache_provenance'][category]): raise RuntimeError('Incomplete dependency verification')
    timer=cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer'])
    if not timer.decode().strip().endswith('active'): raise RuntimeError('Idle timer readiness not proven')
    for nic in before['networkInterfaces']:
        for config in nic.get('accessConfigs',[]):
            cloud(['compute','instances','delete-access-config',VM,'--network-interface='+nic['name'],'--access-config-name='+config['name']])
    after=describe()
    if any(nic.get('accessConfigs') for nic in after['networkInterfaces']): raise RuntimeError('External access configuration remains')
    cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=systemctl is-active quantyra-idle-shutdown.timer'])
    result=dict(vm_id=ID,dependency_preflight=preflight,idle_timer_restored=True,external_ip_removed=True,iap_ssh_verified_without_external_ip=True,before=before,after=after,compiler_invoked=False)
    (receipt/'bootstrap-finalized.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(receipt=str(receipt),idle_timer_restored=True,external_ip_removed=True,iap_ssh_verified_without_external_ip=True)),flush=True)

if __name__ == '__main__': main()
