"""Derive read-only original trace process/output observation with unchanged trusted transport."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'inspect_full109_trace_recovery_progress_v2.py'
    raw = source.read_text(encoding='utf-8')
    nodes = [n for n in ast.walk(ast.parse(raw)) if isinstance(n, ast.Assign)
             and any(isinstance(t, ast.Name) and t.id == 'remote' for t in n.targets)]
    assert len(nodes) == 1
    old_remote = ast.literal_eval(nodes[0].value)
    remote = '''import json,os,shutil,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as s:
 assert s.headers.get('Metadata-Flavor')=='Google' and s.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
marker=json.loads((home/'full109-consumption-v3-launch-once.json').read_bytes())
assert marker['run']=='cmmsa_a8_output_20261010T110328Z_0d5c26f4'
root=home/'full109-consumption-v3-evidence'
rows={}
for name in ('active-process.json','probe.native-exit','terminal.json'):
 p=root/name
 if p.exists():rows[name]=p.read_text()
sizes={name:(root/name).stat().st_size for name in ('probe.stdout','probe.stderr') if (root/name).exists()}
pids=[]
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip();args=(entry/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError):continue
 if name in ('lean','lake') or (name=='python3' and 'full109_consumption_v3_worker.py' in args):pids.append(dict(pid=int(entry.name),name=name,argv=args))
print(json.dumps(dict(run=marker['run'],records=rows,output_bytes=sizes,live_processes=pids,disk_available_bytes=shutil.disk_usage(home).free,archive_present=(home/'full109-consumption-v3-evidence.tar.gz').exists(),read_only=True,trace_replayed=False)))
'''
    literal = ast.get_source_segment(raw, nodes[0].value)
    assert raw.count(literal) == 1 and ast.literal_eval(literal) == old_remote
    updated = raw.replace(literal, repr(remote)).replace("ROOT/'trace-recovery-progress-v2'/", "ROOT/'live-trace-inspections-v1'/")
    assert updated.count("ROOT/'live-trace-inspections-v1'/") == 1
    compile(updated, 'inspect_full109_live_trace_v1.py', 'exec')
    target = HERE / 'inspect_full109_live_trace_v1.py'
    target.open('x', encoding='utf-8', newline='\n').write(updated)
    ledger = dict(source=source.name, source_sha256=digest(source), successor=target.name,
        successor_sha256=digest(target), exact_guest_code=remote,
        unchanged_trusted_host_key_transport=True, no_vm_power_or_compiler_invocation=True,
        original_controller_retained=True, inspection_only=True)
    (HERE / 'full109-live-trace-inspector-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(ledger, indent=2)+'\n')
    print(json.dumps(ledger))


if __name__ == '__main__':
    main()
