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
assert not (home/'full109-exact-crosslevel-warning-repair-resource02-launch-once.json').exists()
rows=[]
for n in range(4,9):
 folder=home/('full109-storage-cache-repoint-v'+str(n));row=dict(scope=n,final_receipt_present=(folder/'receipt.json').is_file())
 partial=folder/'partial-execution.json'
 if partial.is_file():
  try:row['recorded_applied_rows']=len(json.loads(partial.read_bytes())['applied'])
  except json.JSONDecodeError:row['concurrent_nonatomic_partial_write_observed']=True
 rows.append(row)
pids=[]
for entry in Path('/proc').iterdir():
 if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
 try:args=(entry/'cmdline').read_bytes().split(b'\\0')
 except (FileNotFoundError,PermissionError):continue
 if any(arg.endswith(('/full109_storage_cache_repoint_v'+str(n)+'.py').encode()) for n in range(4,9) for arg in args) and b'--execute' in args:pids.append(int(entry.name))
mem=int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))*1024
print(json.dumps(dict(scopes=rows,recovery_pids=pids,disk_available_bytes=shutil.disk_usage(home).free,available_memory_bytes=mem,read_only=True,compiler_invoked=False,launch_clearance=False)))
'''
base=(here/'inspect_full109_recovery_via_openssh.py').read_text()
start=base.index('            remote = """');end=base.index('            command = ',start)
base=base[:start]+'            remote = '+repr(remote)+'\n'+base[end:]
base=base.replace("'openssh-recovery-inspections'", "'concurrent-recovery-progress-inspections-v1'")
target=here/'inspect_full109_concurrent_recovery_progress_v1.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(base)
ast.parse(base)
print('Derived read-only progress inspector; snapshots do not replace complete receipt audit')
