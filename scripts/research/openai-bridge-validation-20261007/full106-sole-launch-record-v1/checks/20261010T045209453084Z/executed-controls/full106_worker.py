"""One dedicated GCP attempt; immutable host guard, no VM power operations."""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys
import tarfile
import traceback
import urllib.error
import urllib.request
from full106_verify import digest

def require_no_external_ip(opener=None):
    opener=opener or urllib.request.build_opener(urllib.request.ProxyHandler({}))
    request=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/network-interfaces/0/access-configs/0/external-ip',headers={'Metadata-Flavor':'Google'})
    try:
        with opener.open(request,timeout=10) as response:
            if response.headers.get('Metadata-Flavor') != 'Google' or response.read().strip():
                raise RuntimeError('External IP remains attached or metadata response is unauthenticated')
    except urllib.error.HTTPError as error:
        if error.code != 404: raise

def execute(stage, run):
    if sys.platform != 'linux': raise RuntimeError('GCP Linux required')
    if not re.fullmatch(r'cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}',run): raise ValueError('Invalid run')
    stage = Path(stage).resolve(strict=True)
    binding = json.loads((stage/'resource-binding.json').read_bytes())
    preflight = json.loads((stage/'dependency-preflight.json').read_bytes())
    home = Path.home().resolve()
    resource_tag=preflight.get('resource_tag','full83-resource02')
    if resource_tag not in ('full83-resource02','full84-resource02-warning-clean','full85-resource02','full86-resource02','full87-resource02','full88-resource02','full89-resource02','full106-exact-product-energy-resource02'): raise RuntimeError('Unexpected resource tag')
    prepared = home/(resource_tag+'-prepared')
    if preflight['prepared_workspace'] != str(prepared): raise RuntimeError('Prepared workspace mismatch')
    if digest(prepared/'cloud_capture.py') != binding['helper_sha256']: raise RuntimeError('Helper drift')
    if digest(prepared/'capture-manifest.json') != binding['files']['capture-manifest.json']: raise RuntimeError('Manifest drift')
    manifest = json.loads((prepared/'capture-manifest.json').read_bytes())
    if {name:digest(prepared/name) for name in binding['auxiliary_inputs']} != binding['auxiliary_inputs']: raise RuntimeError('Prepared axiom harness drift')
    helper = runpy.run_path(str(prepared/'cloud_capture.py'),run_name='dedicated_prelaunch')
    identity = helper['require_gcp'](manifest)
    if identity['id'] != '7237681467779354904' or identity['name'] != 'quantyra-lean-builder-02': raise RuntimeError('Dedicated host mismatch')
    if identity['machine_type'].rsplit('/',1)[-1] != 'e2-highmem-8': raise RuntimeError('Dedicated machine type mismatch')
    require_no_external_ip()
    if shutil.disk_usage(home).free < 40*1024**3: raise RuntimeError('Insufficient remote storage')
    memory = dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
    if int(memory['MemAvailable'].split()[0])*1024 < 48*1024**3: raise RuntimeError('Insufficient available RAM')
    active = []
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit(): continue
        try: name=(entry/'comm').read_text().strip()
        except (FileNotFoundError,PermissionError): continue
        if name in ('lean','lake'): active.append(int(entry.name))
    if active: raise RuntimeError('Existing compiler processes: '+repr(active))
    if subprocess.run(['systemctl','is-active','--quiet','quantyra-idle-shutdown.timer']).returncode:
        raise RuntimeError('Dedicated idle safety timer must be restored before launch')
    warm = home/manifest['cache_provenance']['run']
    toolchain = home/'.elan/toolchains/leanprover--lean4---v4.34.0-rc2'
    if digest(toolchain/'bin/lean') != manifest['cache_provenance']['compiler']['sha256']:
        raise RuntimeError('Compiler identity drift')
    for category,root in [('package_sources',warm),('core_sources',toolchain)]:
        for rel,pin in manifest['cache_provenance'][category].items():
            path=root/rel
            if not path.resolve(strict=True).is_relative_to(root.resolve()) or digest(path) != pin:
                raise RuntimeError(category+' drift: '+rel)
    for rel,pin in manifest['cache_provenance']['objects'].items():
        if digest(warm/rel) != pin: raise RuntimeError('Warm cache drift: '+rel)
    helper['source_pins'](prepared,manifest)
    marker = home/(resource_tag+'-launch-once.json')
    with marker.open('x') as stream:
        json.dump(dict(run=run,host=identity,binding=binding,utc=datetime.now(timezone.utc).isoformat()),stream,indent=2)
    work = home/run
    evidence = home/(run+'_evidence')
    evidence.mkdir()
    failure=None; codes={}
    try:
        shutil.copytree(prepared,work)
        # Independent cache on this dedicated VM: no writes to the preserved warm baseline.
        result=subprocess.run(['cp','-a','--reflink=auto',str(warm/'.lake'),str(work/'.lake')])
        if result.returncode: raise RuntimeError('Owned cache copy failed')
        offline=work/'offline-bin'; offline.mkdir()
        shim=offline/'git'
        shim.write_text('#!/usr/bin/env bash\nfor argument in "$@"; do case "$argument" in clone|fetch|pull|push|ls-remote|submodule) exit 93;; esac; done\nexec /usr/bin/git "$@"\n')
        shim.chmod(0o755)
        env=dict(os.environ); env['PATH']=str(offline)+':'+str(home/'.elan/bin')+':'+env['PATH']
        (evidence/'resource-binding.json').write_bytes((stage/'resource-binding.json').read_bytes())
        (evidence/'capture-manifest.json').write_bytes((work/'capture-manifest.json').read_bytes())
        (evidence/'auxiliary-before.json').write_text(json.dumps({name:digest(work/name) for name in binding['auxiliary_inputs']})+'\n')
        for action in ('begin','compile','finish'):
            if action == 'compile' and codes.get('begin') != 0: continue
            with (evidence/(action+'.stdout')).open('xb') as out,(evidence/(action+'.stderr')).open('xb') as err:
                child=subprocess.Popen([sys.executable,str(work/'cloud_capture.py'),action,str(evidence)],cwd=work,env=env,stdout=out,stderr=err)
                (evidence/'active-process.json').write_text(json.dumps(dict(pid=child.pid,action=action))+'\n')
                codes[action]=child.wait()
            (evidence/(action+'.native-exit')).write_text(str(codes[action])+'\n')
        helper['source_pins'](work,manifest)
        auxiliary_after={name:digest(work/name) for name in binding['auxiliary_inputs']}
        if auxiliary_after != binding['auxiliary_inputs']: raise RuntimeError('Compiled axiom harness drift')
        (evidence/'auxiliary-after.json').write_text(json.dumps(auxiliary_after)+'\n')
        for rel,pin in manifest['cache_provenance']['objects'].items():
            if digest(warm/rel) != pin: raise RuntimeError('Preserved warm baseline drift: '+rel)
    except Exception:
        failure=traceback.format_exc()
    terminal=dict(run=run,host=identity,native_exits=codes,failure=failure,vm_power_operations=False,
                  compiler_host='GCP only',warm_baseline_preserved=failure is None,
                  accepted=codes == {'begin':0,'compile':0,'finish':0} and failure is None)
    (evidence/'dedicated-worker-terminal.json').write_text(json.dumps(terminal,indent=2)+'\n')
    (evidence/'terminal.utc').write_text(datetime.now(timezone.utc).isoformat()+'\n')
    archive=evidence.with_name(evidence.name+'.tar.gz')
    with tarfile.open(archive,'w:gz') as output:
        for path in sorted(evidence.iterdir()): output.add(path,arcname=path.name)
    print(json.dumps(dict(archive=str(archive),sha256=digest(archive),size=archive.stat().st_size,terminal=terminal)),flush=True)
    return 0 if terminal['accepted'] else 1

if __name__ == '__main__': raise SystemExit(execute(*sys.argv[1:]))
