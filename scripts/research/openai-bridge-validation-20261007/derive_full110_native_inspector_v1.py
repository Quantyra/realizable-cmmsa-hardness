"""Bind the preserved read-only IAP/OpenSSH transport to the sole Full110 native run."""
import ast
import hashlib
import json
from pathlib import Path
from custody_checks import digest
from full110_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'inspect_full109_live_trace_v1.py'
    assert digest(source) == '86676B708182ABBA74182AABE0311D2C7C578993780EED8DA5F50F3CB5701317'
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    run = marker['run']
    assert run == 'cmmsa_a8_output_20261011T025221Z_7046a7c0'
    remote = '''import base64,hashlib,json,os,shutil,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as response:
 assert response.headers.get('Metadata-Flavor')=='Google' and response.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
marker=json.loads((home/'full110-exact-real-complex-operators-resource02-launch-once.json').read_bytes())
assert marker['run']=='cmmsa_a8_output_20261011T025221Z_7046a7c0'
root=home/(marker['run']+'_evidence')
records={}
for name in ('active-process.json','begin.native-exit','compile.native-exit','finish.native-exit','aggregate.native-exit','dedicated-worker-terminal.json'):
 p=root/name
 if p.exists():records[name]=p.read_text()
stages=[];streams={}
for number in range(1,8):
 p=root/('stage-'+str(number)+'.command.json')
 if p.exists():stages.append(json.loads(p.read_bytes()))
for p in sorted(root.iterdir()):
 if p.is_file() and p.suffix in ('.stdout','.stderr'):
  assert p.stat().st_size<=16*1024**2,'Unbounded stream; no truncation permitted'
  data=p.read_bytes()
  streams[p.name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper(),base64=base64.b64encode(data).decode())
pids=[]
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip();args=(entry/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError):continue
 if name in ('lean','lake') or (name=='python3' and ('full110_worker.py' in args or marker['run'] in args)):pids.append(dict(pid=int(entry.name),name=name,argv=args))
print(json.dumps(dict(run=marker['run'],records=records,stages=stages,streams=streams,live_processes=pids,disk_available_bytes=shutil.disk_usage(home).free,archive_present=(home/(marker['run']+'_evidence.tar.gz')).exists(),read_only=True,compiler_replayed=False,observed_snapshots_not_authoritative_terminal_custody=True)))
'''
    before = source.read_text(encoding='utf-8')
    lines = before.splitlines(keepends=True)
    old_remote = next(line for line in lines if line.startswith('            remote = '))
    replacements = [
        ('from full109_builder02_controller import ROOT', 'from full110_builder02_controller import ROOT'),
        ('from full109_capture_gates import validate_successor', 'from full110_capture_gates import validate_successor'),
        ('cmmsa_a8_output_20261010T110328Z_0d5c26f4', run),
        ("'live-trace-inspections-v1'", "'live-native-inspections-v1'")]
    after = before
    # Replace the guest script before the one remaining local run-identity substitution.
    assert after.count(old_remote) == 1
    after = after.replace(old_remote, '            remote = '+repr(remote)+'\n')
    for old, new in replacements:
        assert after.count(old) == 1
        after = after.replace(old, new)
    old_output = "            print(json.dumps(dict(folder=str(folder), inspection=result, host_key_fingerprint=fingerprint)), flush=True)\n"
    new_output = '''            decoded = folder / 'observed-streams'; decoded.mkdir()
            for name, row in result['streams'].items():
                assert Path(name).name == name
                data = base64.b64decode(row['base64'], validate=True)
                assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
                (decoded / name).open('xb').write(data)
            print(json.dumps(dict(folder=str(folder), run=result['run'], stage_exits=[r['native_exit'] for r in result['stages']], live_processes=result['live_processes'], observed_streams=len(result['streams']), disk_available_bytes=result['disk_available_bytes'], authoritative_terminal_custody=False)), flush=True)
'''
    assert after.count(old_output) == 1
    after = after.replace(old_output, new_output)
    ast.parse(after)
    target = HERE / 'inspect_full110_native_progress_v1.py'
    target.open('xb').write(after.encode('utf-8'))
    record = dict(source=str(source), source_sha256=digest(source), target=str(target), target_sha256=digest(target),
                  exact_replacements=replacements, original_remote_script=ast.literal_eval(old_remote.strip()[len('remote = '):]),
                  new_remote_script=remote, old_output=old_output, new_output=new_output,
                  native_run=run, read_only_guest=True, host_key_authentication_preserved=True,
                  complete_observed_streams_without_truncation=True, compiler_invoked=False)
    (HERE / 'full110-native-inspector-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(target=str(target), sha256=digest(target), read_only=True, native_run=run)))


if __name__ == '__main__':
    main()
