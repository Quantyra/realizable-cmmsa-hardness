from pathlib import Path
import ast
here=Path(__file__).parent
text=(here/'boot_full109_readonly_recovery_v1.py').read_text()
text=text.replace("assert not (ROOT/'launch-once.json').exists()","assert not (ROOT/'consumption-v3'/'launch-once.json').exists()")
text=text.replace("ROOT/'readonly-recovery-boot-v1'","ROOT/'consumption-v3'/'settled-cache-recovery-boot-v1'")
text=text.replace('Read-only interrupted recovery inspection','Qualified trace settled-cache recovery after verified termination')
target=here/'boot_full109_trace_cache_recovery_v1.py';ast.parse(text)
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
remote='''import json,subprocess,time,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as s:
 assert s.headers.get('Metadata-Flavor')=='Google' and s.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
events=[];deadline=time.monotonic()+3600
while time.monotonic()<deadline and not (home/'full109-consumption-v3-launch-once.json').exists():
 now=int(time.time())
 p=subprocess.run(['sudo','tee','/var/lib/quantyra-idle-shutdown/last-active'],input=(str(now)+'\\n').encode(),capture_output=True,check=True)
 assert p.stdout.strip()==str(now).encode()
 p=subprocess.run(['systemctl','is-active','quantyra-idle-shutdown.timer'],capture_output=True,check=True);assert p.stdout.strip()==b'active'
 events.append(now);time.sleep(60)
print(json.dumps(dict(refresh_epochs=events,maximum_seconds=3600,timer_disabled=False,compiler_invoked=False,vm_power_operation=False)))
'''
base=(here/'inspect_full109_trace_resources_v1.py').read_text()
start=base.index('            remote = ');end=base.index('            command = ',start)
base=base[:start]+'            remote = '+repr(remote)+'\n'+base[end:]
base=base.replace("'trace-resource-inspections-v1'", "'trace-staging-idle-lease-v1'")
target=here/'maintain_full109_trace_staging_idle_lease_v1.py';ast.parse(base)
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(base)
print('Derived exact recovery boot and bounded idle lease; timer remains enabled')
