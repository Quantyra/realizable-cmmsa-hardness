"""Keep existing idle timer activity current only while exact recovery jobs run."""
from pathlib import Path
import ast
here=Path(__file__).parent
remote='''import json,os,subprocess,time,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as s:
 assert s.headers.get('Metadata-Flavor')=='Google' and s.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
events=[]
while True:
 assert not (home/'full109-exact-crosslevel-warning-repair-resource02-launch-once.json').exists()
 pids=[]
 for entry in Path('/proc').iterdir():
  if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
  try:args=(entry/'cmdline').read_bytes().split(b'\\0')
  except (FileNotFoundError,PermissionError):continue
  if any(arg.endswith(('/full109_storage_cache_repoint_v'+str(n)+'.py').encode()) for n in range(4,9) for arg in args) and b'--execute' in args:pids.append(int(entry.name))
 if not pids:break
 now=int(time.time())
 touched=subprocess.run(['sudo','tee','/var/lib/quantyra-idle-shutdown/last-active'],input=(str(now)+'\\n').encode(),capture_output=True,check=True)
 assert touched.stdout.strip()==str(now).encode()
 active=subprocess.run(['systemctl','is-active','quantyra-idle-shutdown.timer'],capture_output=True,check=True)
 assert active.stdout.strip()==b'active'
 events.append(dict(epoch=now,exact_recovery_pids=pids,timer_active=True))
 time.sleep(60)
print(json.dumps(dict(events=events,all_recovery_processes_terminal=True,only_idle_activity_updated=True,timer_disabled=False,vm_power_operation=False,compiler_invoked=False)))
'''
base=(here/'inspect_full109_recovery_via_openssh.py').read_text()
start=base.index('            remote = """');end=base.index('            command = ',start)
base=base[:start]+'            remote = '+repr(remote)+'\n'+base[end:]
base=base.replace("'openssh-recovery-inspections'", "'recovery-idle-keeper-controls-v1'")
base=base.replace('"""Read existing scope3 state via IAP/OpenSSH and the already trusted host key."""',
 '"""Maintain idle activity during exact cache jobs; no VM power/compile/recovery operation."""')
target=here/'keep_full109_recovery_idle_activity_v1.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(base)
ast.parse(base)
print('Derived idle keeper: exact jobs only, exits once jobs end, idle timer remains enabled')
