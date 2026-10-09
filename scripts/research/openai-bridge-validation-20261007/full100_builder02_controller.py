"""Full83 resource-02 controller: default read-only gates; explicit one-attempt execution."""
import sys
sys.dont_write_bytecode = True
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import tarfile
import uuid
from shared_controller import context, heads, HEAD, ORIGIN, MANIFEST_SHA
from custody_checks import digest, verify_local_custody

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02')
STAGE = '/home/dfredriksen_quantyra_org/full100-matrix-fourier-bullet-repair-builder02-stage'
VM = 'quantyra-lean-builder-02'
VM_ID = '7237681467779354904'
NAMES = ('extract_builder02_dependencies.py','full100_verify.py','full100_worker.py')
EXTRA_LOCAL_CONTROLS = ('full100_capture_gates.py','prepare_builder02_full100.py','full100_native_audit.py','full100_postprocess.py','derive_full100_execution_controls.py','prepare_full100_bullet_candidates.py')

def save(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream: json.dump(value,stream,indent=2)

def local_gates(common,loaded):
    capture=common.PACKAGE/'captures/capture-full-a22-hc46-83'
    if digest(capture/'manifest.json') != MANIFEST_SHA: raise RuntimeError('Original capture drift')
    common.verify_capture(capture,live=False)
    if heads(common.REPO) != {'head':HEAD,'origin_main':ORIGIN}: raise RuntimeError('Frozen Git context drift')
    if common.inherited_now() != json.loads((capture/'inherited-files-before.json').read_bytes()): raise RuntimeError('Inherited file drift')
    if common.inherited_status_now() != json.loads((capture/'inherited-status-before.json').read_bytes()): raise RuntimeError('Approved logical preservation drift')
    for rel,pin in json.loads((loaded['HERE']/'current-dependency-pins.json').read_bytes()).items():
        if digest(common.REPO/rel) != pin: raise RuntimeError('Live dependency drift: '+rel)
    if shutil.disk_usage(ROOT).free < 1536*1024**2: raise RuntimeError('Insufficient local custody reserve')

def audit_terminal(path,run,manifest,common):
    with tarfile.open(path,'r:gz') as archive:
        members=archive.getmembers()
        if len({m.name for m in members}) != len(members): raise RuntimeError('Duplicate evidence entries')
        def read(name):
            member=archive.getmember(name)
            if not member.isfile(): raise RuntimeError('Non-file evidence entry')
            return archive.extractfile(member).read()
        terminal=json.loads(read('dedicated-worker-terminal.json'))
        if terminal['run'] != run or terminal['host']['id'] != VM_ID or terminal['host']['name'] != VM:
            raise RuntimeError('Foreign terminal evidence')
        if terminal['failure'] is not None or terminal['native_exits'].get('finish') != 0:
            raise RuntimeError('Worker completion unresolved; preserve VM and receipts')
        green=terminal['native_exits'] == {'begin':0,'compile':0,'finish':0}
        stages=[]; profiles={}
        for i,stage in enumerate(manifest['stages']):
            if stage['index'] != i: raise RuntimeError('Unexpected stage index')
            if terminal['native_exits'].get('begin') != 0: break
            code=int(read('stage-'+str(i)+'.native-exit'))
            command=json.loads(read('stage-'+str(i)+'.command.json'))
            out=read('stage-'+str(i)+'.stdout'); err=read('stage-'+str(i)+'.stderr')
            if command['native_exit'] != code or command['gcp_instance_id'] != VM_ID: raise RuntimeError('Stage receipt mismatch')
            if command['stage'] != stage or command['argv'] != ['timeout','--signal=TERM','--kill-after=20s','900s',*stage['argv']]:
                raise RuntimeError('Stage scope or invocation drift')
            import hashlib
            if command['stdout_sha256'] != hashlib.sha256(out).hexdigest().upper() or command['stderr_sha256'] != hashlib.sha256(err).hexdigest().upper():
                raise RuntimeError('Stage output hash mismatch')
            counts=common.diagnostic_counts(out.decode(errors='replace'),err.decode(errors='replace'))
            if green and (code or counts['errors'] or counts['unsolved_goals']): raise RuntimeError('Green terminal contradicted by diagnostics')
            profiles.update(common.axiom_profiles(out.decode(errors='replace')))
            stages.append(dict(index=i,native_exit=code,diagnostics=counts))
        if green:
            common.require_profiles(profiles)
            missing_or_nonstandard={name:profiles.get(name) for name in manifest['requested_axioms'] if name not in profiles or not set(profiles[name]) <= common.STANDARD_AXIOMS}
            if missing_or_nonstandard: raise RuntimeError('Full192 standard-axiom scope missing or contradicted: '+repr(missing_or_nonstandard))
            binding=json.loads(read('resource-binding.json'))
            if json.loads(read('auxiliary-before.json')) != binding['auxiliary_inputs'] or json.loads(read('auxiliary-after.json')) != binding['auxiliary_inputs']: raise RuntimeError('Fresh harness custody mismatch')
            expected={rel:row['sha256'] for rel,row in manifest['project_sources'].items()}
            expected.update({rel:row['sha256'] for rel,row in manifest['configs'].items()})
            if json.loads(read('source-before.json')) != expected or json.loads(read('source-after.json')) != expected:
                raise RuntimeError('Compiled source custody mismatch')
            cache=manifest['cache_provenance']
            if json.loads(read('verified-cache-provenance.json')) != cache:
                raise RuntimeError('Cache provenance mismatch')
            for name,category in [('package-source-hashes.json','package_sources'),('core-source-hashes.json','core_sources'),('compiler-identity.json','compiler')]:
                if json.loads(read(name)) != cache[category]: raise RuntimeError('Toolchain/package evidence mismatch')
            objects=json.loads(read('object-after.json'))
            if any(objects.get(rel) != pin for rel,pin in cache['objects'].items()): raise RuntimeError('Cached dependency objects changed')
        return dict(native_terminal=True,compile_green=green,stages=stages,axiom_profiles=len(profiles),reviews_required=True)

def main(execute=False):
    from full100_capture_gates import validate_successor
    validate_successor()
    loaded,runner=context(); common=loaded['common']
    local_gates(common,loaded)
    binding=json.loads((ROOT/'resource-binding.json').read_bytes())
    if binding['vm_id'] != VM_ID or binding['vm'] != VM: raise RuntimeError('Resource binding drift')
    for name,pin in binding['files'].items():
        if digest(ROOT/name) != pin: raise RuntimeError('Resource capsule drift')
    manifest=json.loads((ROOT/'capture-manifest.json').read_bytes())
    expected={name:digest(Path(__file__).with_name(name)) for name in NAMES}
    expected.update({name:digest(ROOT/name) for name in ('input-archive.tar.gz','capture-manifest.json','resource-binding.json')})
    runner.VM=VM
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    check=ROOT/'checks'/stamp; check.mkdir(parents=True)
    class DedicatedControl(runner.Control):
        def cloud(self,args,**kwargs):
            if args[:3] != ['compute','instances','describe'] and args[:2] not in (['compute','ssh'],['compute','scp']):
                raise RuntimeError('Controller permits only inspection and owned transport')
            return super().cloud(args,**kwargs)
        def describe(self):
            _,out,_=self.cloud(['compute','instances','describe',VM,'--format=json(name,id,status,zone,machineType,networkInterfaces)'])
            value=json.loads(out)
            if value.get('name') != VM or str(value.get('id')) != VM_ID or value.get('zone','').rsplit('/',1)[-1] != 'us-central1-a': raise RuntimeError('Unexpected GCP identity')
            if value.get('machineType','').rsplit('/',1)[-1] != 'e2-highmem-8': raise RuntimeError('Unexpected machine type')
            return value
    control=DedicatedControl(check)
    state=control.describe()
    if state['status'] != 'RUNNING': raise RuntimeError('Dedicated VM not running; inspect existing state')
    if any(nic.get('accessConfigs') for nic in state['networkInterfaces']): raise RuntimeError('Temporary external IP must be removed before launch')
    control.authenticated=True
    _,out,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=sha256sum '+' '.join(STAGE+'/'+name for name in expected)])
    if {line.split()[1].rsplit('/',1)[1]:line.split()[0].upper() for line in out.decode().splitlines()} != expected: raise RuntimeError('Staged control/capsule drift')
    _,out,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=cat '+STAGE+'/dependency-preflight.json'])
    remote=json.loads(out)
    if remote['prepared_workspace'] != '/home/dfredriksen_quantyra_org/'+ROOT.name+'-prepared':
        raise RuntimeError('Prepared resource workspace mismatch')
    for field,category in [('package_sources_verified','package_sources'),('core_sources_verified','core_sources'),('warm_objects_verified','objects')]:
        if remote[field] != len(manifest['cache_provenance'][category]): raise RuntimeError('Incomplete dependency verification')
    if remote['project_sources_verified'] != 327: raise RuntimeError('Incomplete project source verification')
    if len(manifest['requested_axioms']) != 192: raise RuntimeError('Incomplete profile scope')
    if remote['auxiliary_inputs_verified'] != binding['auxiliary_inputs']: raise RuntimeError('Fresh harness preflight drift')
    if remote['gcp_identity']['id'] != VM_ID or remote['compiler_sha256'] != manifest['cache_provenance']['compiler']['sha256']: raise RuntimeError('Dependency identity mismatch')
    save(check/'preflight.json',dict(local_preservation=True,authenticated_vm=state,remote_dependencies=remote,execute_requested=execute))
    if not execute:
        print(json.dumps(dict(preflight=str(check),passed=True,launch_called=False))); return 0
    marker=ROOT/'launch-once.json'
    run='cmmsa_a8_output_'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'_'+uuid.uuid4().hex[:8]
    save(marker,dict(run=run,preflight=str(check),controller_sha256=digest(__file__),remote_controls=expected,
                     extra_local_controls={name:digest(Path(__file__).with_name(name)) for name in EXTRA_LOCAL_CONTROLS}))
    executed=check/'executed-controls'; executed.mkdir()
    for name in (*NAMES,'full100_builder02_controller.py',*EXTRA_LOCAL_CONTROLS):
        shutil.copyfile(Path(__file__).with_name(name),executed/name)
    code,_,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=python3 -B '+STAGE+'/full100_worker.py '+STAGE+' '+run],timeout=4350,allow_failure=True)
    archive='/home/dfredriksen_quantyra_org/'+run+'_evidence.tar.gz'
    _,out,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=sha256sum '+archive+'; stat -c %s '+archive])
    lines=out.decode().splitlines(); sha=lines[0].split()[0].upper(); size=int(lines[1])
    short=Path('C:/a8gcp')/(run.rsplit('_',1)[1]+'.tar.gz')
    if short.exists(): raise RuntimeError('Custody path collision')
    control.cloud(['compute','scp',VM+':'+archive,str(short),'--tunnel-through-iap'],timeout=300)
    second=check/(run+'_evidence.tar.gz')
    with short.open('rb') as source,second.open('xb') as target: shutil.copyfileobj(source,target)
    custody=verify_local_custody(short,second,sha,size)
    custody['vm_retained_for_other_threads']=False
    terminal=audit_terminal(second,run,manifest,common)
    local_gates(common,loaded)
    save(check/'terminal-custody.json',dict(run=run,ssh_native_exit=code,custody=custody,terminal=terminal,vm_stop_performed=False))
    print(json.dumps(dict(run=run,check=str(check),terminal=terminal)),flush=True)
    return 0 if terminal['compile_green'] else 1

if __name__ == '__main__':
    if sys.argv[1:] not in ([],['--execute']): raise SystemExit('Default preflight or --execute required')
    raise SystemExit(main(sys.argv[1:] == ['--execute']))
