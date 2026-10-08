"""GCP-only dependency and resource-capsule preflight. No compiler invocation."""
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import sys
import tarfile

def digest(path):
    with Path(path).open('rb') as stream: return hashlib.file_digest(stream,'sha256').hexdigest().upper()

def verify(stage,resource_tag='full83-resource02'):
    if sys.platform != 'linux': raise RuntimeError('GCP Linux required')
    stage = Path(stage).resolve(strict=True)
    binding = json.loads((stage/'resource-binding.json').read_bytes())
    for name,pin in binding['files'].items():
        if digest(stage/name) != pin: raise RuntimeError('Capsule drift: '+name)
    home = Path.home().resolve()
    if str(home) != '/home/dfredriksen_quantyra_org': raise RuntimeError('Unexpected home')
    if resource_tag not in ('full83-resource02','full84-resource02-warning-clean','full85-resource02'): raise RuntimeError('Unexpected resource tag')
    work = home/(resource_tag+'-prepared')
    if work.exists(): raise RuntimeError('Prepared workspace already exists; inspect it before continuing')
    work.mkdir()
    with tarfile.open(stage/'input-archive.tar.gz','r:gz') as archive:
        members = archive.getmembers()
        if len({m.name for m in members}) != len(members): raise RuntimeError('Duplicate capsule entries')
        for member in members:
            if not member.isfile() or member.name.startswith('/') or any(p in ('','.','..') for p in member.name.split('/')):
                raise RuntimeError('Unsafe capsule member')
            target = work/member.name
            target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as stream: stream.write(archive.extractfile(member).read())
    if digest(work/'cloud_capture.py') != binding['helper_sha256']: raise RuntimeError('Helper drift')
    manifest = json.loads((work/'capture-manifest.json').read_bytes())
    helper = runpy.run_path(str(work/'cloud_capture.py'),run_name='prelaunch_only')
    identity = helper['require_gcp'](manifest)
    helper['source_pins'](work,manifest)
    cache = manifest['cache_provenance']
    warm = home/cache['run']
    toolchain = home/'.elan/toolchains/leanprover--lean4---v4.34.0-rc2'
    compiler = toolchain/'bin/lean'
    if digest(compiler) != cache['compiler']['sha256']: raise RuntimeError('Compiler drift')
    for category,root in [('package_sources',warm),('objects',warm),('core_sources',toolchain)]:
        for rel,pin in cache[category].items():
            candidate = root/rel
            if not candidate.resolve(strict=True).is_relative_to(root.resolve()): raise RuntimeError('Pin escapes root')
            if digest(candidate) != pin: raise RuntimeError(category+' drift: '+rel)
    receipt = dict(gcp_identity=identity,project_sources_verified=len(manifest['project_sources']),
        package_sources_verified=len(cache['package_sources']),core_sources_verified=len(cache['core_sources']),
        warm_objects_verified=len(cache['objects']),compiler_sha256=digest(compiler),
        disk_available_bytes=shutil.disk_usage(home).free,compiler_invoked=False,launch_clearance=False,
        prepared_workspace=str(work),resource_tag=resource_tag)
    (stage/'dependency-preflight.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__': verify(*sys.argv[1:])
