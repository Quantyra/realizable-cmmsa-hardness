from pathlib import Path
import ast
here=Path(__file__).parent
remote='''import json,os,shutil,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as s:
 assert s.headers.get('Metadata-Flavor')=='Google' and s.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
assert not (home/'full109-consumption-v3-launch-once.json').exists()
pids=[]
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:name=(entry/'comm').read_text().strip()
 except (FileNotFoundError,PermissionError):continue
 if name in ('lean','lake','cp','tar'):pids.append(dict(pid=int(entry.name),name=name))
mem=int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))*1024
print(json.dumps(dict(disk_available_bytes=shutil.disk_usage(home).free,available_memory_bytes=mem,
 active_compiler_or_copy=pids,trace_once_present=False,read_only=True,trace_executed=False)))
'''
base=(here/'inspect_full109_native_progress_v1.py').read_text()
start=base.index('            remote = ');end=base.index('            command = ',start)
base=base[:start]+'            remote = '+repr(remote)+'\n'+base[end:]
base=base.replace("'native-progress-inspections-v1'", "'trace-resource-inspections-v1'")
target=here/'inspect_full109_trace_resources_v1.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(base)
ast.parse(base)
print('Derived read-only trace resource inspector')
