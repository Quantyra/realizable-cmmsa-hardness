"""One GCP-only metadata probe against qualified Full95 objects; no VM power."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tarfile
import traceback

def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest().upper()

def execute(stage, launch=False):
    if sys.platform != 'linux':
        raise RuntimeError('GCP Linux required')
    home = Path('/home/dfredriksen_quantyra_org')
    stage = Path(stage).resolve(strict=True)
    if stage != home/'full95-consumption-v1-stage':
        raise RuntimeError('Unexpected stage')
    binding = json.loads((stage/'green-binding.json').read_bytes())
    if binding['resource'] != 'full95-manuscript-moment-syntax-repair-resource02' or not binding['qualified_native_green']:
        raise RuntimeError('Qualified native GREEN required')
    run = binding['run']
    if run != 'cmmsa_a8_output_20261009T023928Z_13a1218e':
        raise RuntimeError('Unexpected compiled run')
    work = home/run
    native = home/(run+'_evidence.tar.gz')
    if digest(native) != binding['native_archive_sha256']:
        raise RuntimeError('Native custody mismatch')
    with tarfile.open(native) as archive:
        manifest = json.loads(archive.extractfile('capture-manifest.json').read())
        objects = json.loads(archive.extractfile('object-after.json').read())
        for i in range(7):
            if int(archive.extractfile('stage-'+str(i)+'.native-exit').read()) != 0:
                raise RuntimeError('Native stage is not GREEN')
    if digest(work/'capture-manifest.json') != binding['capture_manifest_sha256']:
        raise RuntimeError('Manifest drift')
    if digest(work/'cloud_capture.py') != binding['helper_sha256']:
        raise RuntimeError('Capture helper drift')
    helper = runpy.run_path(str(work/'cloud_capture.py'), run_name='consumption_preflight')
    identity = helper['require_gcp'](manifest)
    if identity['id'] != '7237681467779354904' or identity['name'] != 'quantyra-lean-builder-02':
        raise RuntimeError('Foreign GCP resource')
    if identity['machine_type'].rsplit('/', 1)[-1] != 'e2-highmem-8':
        raise RuntimeError('Unexpected machine type')
    original_stage = home/'full95-manuscript-moment-syntax-repair-builder02-stage'
    for name, pin in binding['original_remote_controls'].items():
        if digest(original_stage/name) != pin:
            raise RuntimeError('Original remote control drift')
    sys.path.insert(0, str(original_stage))
    from full95_worker import require_no_external_ip
    require_no_external_ip()
    if shutil.disk_usage(home).free < 40*1024**3:
        raise RuntimeError('Insufficient remote storage')
    memory = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    if int(memory['MemAvailable'].split()[0])*1024 < 48*1024**3:
        raise RuntimeError('Insufficient available RAM')
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            name = (entry/'comm').read_text().strip()
        except (FileNotFoundError, PermissionError):
            continue
        if name in ('lean', 'lake'):
            raise RuntimeError('Another compiler process exists')
    if subprocess.run(['systemctl', 'is-active', '--quiet', 'quantyra-idle-shutdown.timer']).returncode:
        raise RuntimeError('Idle timer is not active')
    toolchain = home/'.elan/toolchains/leanprover--lean4---v4.34.0-rc2'
    if digest(toolchain/'bin/lean') != manifest['cache_provenance']['compiler']['sha256']:
        raise RuntimeError('Compiler drift')
    project_objects = {'.lake/build/lib/lean/'+rel.removeprefix('lean/').removesuffix('.lean')+'.olean'
                       for rel in manifest['project_sources']}
    if len(project_objects) != 323 or not project_objects <= set(objects):
        raise RuntimeError('Incomplete native object closure')
    def preserved():
        helper['source_pins'](work, manifest)
        for rel, pin in objects.items():
            path = work/rel
            if not path.resolve(strict=True).is_relative_to(work.resolve()) or digest(path) != pin:
                raise RuntimeError('Compiled object drift: '+rel)
        for category, root in [('package_sources', work), ('core_sources', toolchain)]:
            for rel, pin in manifest['cache_provenance'][category].items():
                path = root/rel
                if not path.resolve(strict=True).is_relative_to(root.resolve()) or digest(path) != pin:
                    raise RuntimeError(category+' drift: '+rel)
    preserved()
    readiness = binding['tooling_readiness']
    if (readiness['requested_roots_exact'],readiness['focused_consumers_exact']) != (181,13): raise RuntimeError('Expanded material probe scope differs')
    if digest(stage/'tooling.tar.gz') != readiness['tooling_archive_sha256']:
        raise RuntimeError('Probe tooling archive drift')
    if readiness['capture_manifest_sha256'] != binding['capture_manifest_sha256']:
        raise RuntimeError('Probe is bound to a different capture')
    if not launch:
        print(json.dumps(dict(passed=True, launch_called=False, identity=identity,
                              project_sources=323, compiled_objects=len(objects))), flush=True)
        return 0
    output = home/'full95-consumption-v1-evidence'
    with (home/'full95-consumption-v1-launch-once.json').open('x', encoding='utf-8') as marker:
        json.dump(dict(run=run, binding=binding, identity=identity, utc=datetime.now(timezone.utc).isoformat()), marker, indent=2)
    output.mkdir()
    tooling = output/'tooling'; tooling.mkdir()
    with tarfile.open(stage/'tooling.tar.gz') as archive:
        members = archive.getmembers()
        if len(members) != 3 or {m.name for m in members} != set(readiness['files']):
            raise RuntimeError('Unexpected tooling entries')
        for member in members:
            if not member.isfile() or '/' in member.name or '\\' in member.name:
                raise RuntimeError('Unsafe tooling entry')
            data = archive.extractfile(member).read()
            row = readiness['files'][member.name]
            if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest().upper() != row['sha256']:
                raise RuntimeError('Tooling file drift')
            (tooling/member.name).write_bytes(data)
    failure = None; code = None
    try:
        env = dict(os.environ)
        env['PATH'] = str(work/'offline-bin')+':'+str(home/'.elan/bin')+':'+env['PATH']
        command = ['lake', 'env', 'lean', str(tooling/'probe.lean')]
        (output/'command.json').write_text(json.dumps(command)+'\n')
        with (output/'probe.stdout').open('xb') as out, (output/'probe.stderr').open('xb') as err:
            child = subprocess.Popen(command, cwd=work, env=env, stdout=out, stderr=err)
            (output/'active-process.json').write_text(json.dumps(dict(pid=child.pid, command=command))+'\n')
            code = child.wait()
        (output/'probe.native-exit').write_text(str(code)+'\n')
        preserved()
    except Exception:
        failure = traceback.format_exc()
    terminal = dict(run=run, identity=identity, probe_native_exit=code, failure=failure,
        project_sources_preserved=323 if failure is None else None,
        compiled_objects_preserved=len(objects) if failure is None else None,
        project_object_closure=323, native_archive_sha256=binding['native_archive_sha256'],
        probe_sha256=readiness['files']['probe.lean']['sha256'],
        consumption_coverage_complete=False, reviewed=False, accepted=False, local_compilation=False)
    (output/'green-binding.json').write_bytes((stage/'green-binding.json').read_bytes())
    (output/'terminal.json').write_text(json.dumps(terminal, indent=2)+'\n')
    archive_path = home/'full95-consumption-v1-evidence.tar.gz'
    with tarfile.open(archive_path, 'w:gz') as archive:
        for path in sorted(output.rglob('*')):
            if path.is_file():
                archive.add(path, arcname=path.relative_to(output).as_posix())
    print(json.dumps(dict(archive=str(archive_path), sha256=digest(archive_path), bytes=archive_path.stat().st_size, terminal=terminal)), flush=True)
    return 0 if code == 0 and failure is None else 1

if __name__ == '__main__':
    if len(sys.argv) < 2 or sys.argv[2:] not in ([], ['--execute']):
        raise SystemExit('Stage path and optional --execute required')
    raise SystemExit(execute(sys.argv[1], sys.argv[2:] == ['--execute']))
