"""Derive custody and read-only transport controls from preserved originals."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROWS = []


def derive(parent, target, changes):
    raw = (HERE / parent).read_bytes()
    committed = subprocess.check_output(['git', 'show', '7d26e6cc:scripts/research/openai-bridge-validation-20261007/' + parent], cwd=HERE)
    assert raw == committed
    value = raw.decode('utf-8')
    for old, new in changes:
        assert value.count(old) == 1, (parent, old[:80], value.count(old))
        value = value.replace(old, new)
    ast.parse(value)
    data = value.encode('utf-8')
    (HERE / target).open('xb').write(data)
    ROWS.append(dict(parent=parent, parent_sha256=hashlib.sha256(raw).hexdigest().upper(),
                     target=target, sha256=hashlib.sha256(data).hexdigest().upper(), changes=changes))


def main():
    derive('preserve_full111_frozen_package_v1.py', 'preserve_full112_frozen_package_v1.py', [
        ('from prepare_builder02_full111 ', 'from prepare_builder02_full112 '),
        ('full111-execution-control-validation-20261011T031402428924Z', 'full112-execution-control-validation-20261011T043143761793Z'),
        ('full111-immutable-package-record-v1', 'full112-immutable-package-record-v1'),
        ('full111-frozen-two-source-repair-and-control-checks-v1', 'full112-frozen-two-source-repair-and-control-checks-v1'),
        ('original_preparation_tool_handle=41254', 'original_preparation_tool_handle=86509'),
        ('original_validation_tool_handle=98666', 'original_validation_tool_handle=91702')])
    source = (HERE / 'inspect_full111_native_progress_v1.py').read_text(encoding='utf-8')
    old_remote = next(line for line in source.splitlines() if line.startswith('            remote = '))
    guest = '''import hashlib,json,os,shutil,subprocess,time,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as response:
 assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
scopes=[]
for number in (111,96,97,98):
 root=home/('full111-settled-cache-native'+str(number)+'-v1')
 files=[]
 if root.exists():
  for p in sorted(root.iterdir()):
   assert p.is_file() and not p.is_symlink()
   data=p.read_bytes();files.append(dict(name=p.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
 scopes.append(dict(number=number,exists=root.exists(),files=files))
pids=[]
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip();args=(entry/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError):continue
 if name in ('lean','lake','cp','tar') or (name=='python3' and any(t in args for t in ('_worker.py','settled_cache_native','cloud_capture.py'))):pids.append(dict(pid=int(entry.name),name=name,argv=args))
timer=subprocess.run(['systemctl','is-active','quantyra-idle-shutdown.timer'],capture_output=True)
last=Path('/var/lib/quantyra-idle-shutdown/last-active')
print(json.dumps(dict(scopes=scopes,live_processes=pids,disk_available_bytes=shutil.disk_usage(home).free,
 epoch=int(time.time()),idle_last_active=last.read_text() if last.exists() else None,
 timer_exit=timer.returncode,timer_stdout=timer.stdout.decode(),timer_stderr=timer.stderr.decode(),
 full112_launch_present=(home/'full112-exact-real-complex-operators-repair2-resource02-launch-once.json').exists(),
 read_only=True,compiler_invoked=False,planner_replayed=False)))
'''
    begin = source.index("            decoded = folder / 'observed-streams'")
    end = source.index('        finally:', begin)
    derive('inspect_full111_native_progress_v1.py', 'inspect_full111_recovery_state_v1.py', [
        ('    validate_successor()\n    loaded, _ = context()\n    local_gates(loaded[\'common\'], loaded)\n',
         "    failure = ROOT/'research-resume-20261011/20261011T042854525502Z-3c1895f34b07/command.json'\n    assert json.loads(failure.read_bytes())['native_exit'] == 1\n    assert json.loads((ROOT/'settled-cache-recovery-v1/boot-result.json').read_bytes())['after']['status'] == 'RUNNING'\n    # Read-only observation has no compiler or recovery admission authority.\n"),
        ("'live-native-inspections-v1'", "'recovery-state-inspections-v1'"),
        (old_remote, '            remote = ' + repr(guest)),
        (source[begin:end], "            print(json.dumps(dict(folder=str(folder), inspection=result)), flush=True)\n")])
    derive('run_full112_resume_step_v1.py', 'run_full112_resume_step_v2.py', [
        ("ALLOWED = {'stage_full112_builder02.py', 'full112_builder02_controller.py', 'full112_postprocess.py'}",
         "ALLOWED = {'stage_full112_builder02.py', 'stage_full112_after_recovery_v1.py', 'full112_builder02_controller.py', 'full112_postprocess.py', 'preserve_full112_frozen_package_v1.py', 'inspect_full111_recovery_state_v1.py'}")])
    record = dict(schema='full112-checkpoint-control-derivation-v1', parent_commit='7d26e6cc', rows=ROWS,
                  compiler_invoked=False, cloud_operation=False, recovery_or_launch_clearance=False)
    (HERE/'full112-checkpoint-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(derived=len(ROWS), compiler_invoked=False)))


if __name__ == '__main__':
    main()
