"""Derive a read-only observer of the existing six recovery transactions."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).parent
remote = '''import json,os,shutil,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as s:
 assert s.headers.get('Metadata-Flavor')=='Google' and s.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
rows=[]
for number in range(84,90):
 root=home/('full109-trace-cache-small-native'+str(number)+'-v1')
 row=dict(number=number,once=(root/'execute-once.json').exists(),receipt=(root/'receipt.json').exists())
 for name in ('receipt.json','partial-execution.json'):
  path=root/name
  if path.exists():
   try:value=json.loads(path.read_bytes());row[name]=dict(applied=len(value['applied']),disk_after_bytes=value.get('disk_after_bytes'))
   except json.JSONDecodeError:row[name]=dict(observation='concurrent receipt write; not terminal')
 rows.append(row)
pids=[]
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip();args=(entry/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError):continue
 if name in ('lean','lake') or (name=='python3' and 'full109_trace_cache_small_native' in args):pids.append(dict(pid=int(entry.name),name=name,argv=args))
print(json.dumps(dict(rows=rows,live_processes=pids,disk_available_bytes=shutil.disk_usage(home).free,trace_once_present=(home/'full109-consumption-v3-launch-once.json').exists(),read_only=True)))
'''


def main():
    source = HERE/'inspect_full109_trace_resources_v1.py'
    original = source.read_text(encoding='utf-8')
    start = original.index('            remote = ')
    end = original.index('            command = ', start)
    text = original[:start]+'            remote = '+repr(remote)+'\n'+original[end:]
    assert text.count("'trace-resource-inspections-v1'") == 1
    text = text.replace("'trace-resource-inspections-v1'", "'trace-recovery-progress-v2'")
    ast.parse(text)
    target = HERE/'inspect_full109_trace_recovery_progress_v2.py'
    target.open('x', encoding='utf-8', newline='\n').write(text)
    record = dict(parent_sha256=digest(source), target_sha256=digest(target),
                  only_remote_readonly_payload_and_receipt_directory_changed=True,
                  exact_identity_and_trusted_host_guards_retained=True, executed=False)
    (HERE/'full109-trace-progress-inspector-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record))


if __name__ == '__main__':
    main()
