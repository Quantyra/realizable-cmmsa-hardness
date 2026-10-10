from pathlib import Path
import ast
here=Path(__file__).parent
remote='''import json,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as s:
 assert s.headers.get('Metadata-Flavor')=='Google' and s.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
run='cmmsa_a8_output_20261010T110328Z_0d5c26f4'
marker=json.loads((home/'full109-exact-crosslevel-warning-repair-resource02-launch-once.json').read_bytes())
assert marker['run']==run and marker['host']['id']=='7237681467779354904'
folder=home/(run+'_evidence');stages=[];actions={}
for number in range(7):
 path=folder/('stage-'+str(number)+'.native-exit')
 if path.is_file():
  value=path.read_text().strip()
  if value:stages.append(dict(stage=number,native_exit=int(value)))
for action in ('begin','compile','finish'):
 path=folder/(action+'.native-exit')
 if path.is_file():
  value=path.read_text().strip()
  if value:actions[action]=int(value)
print(json.dumps(dict(run=run,stages=stages,actions=actions,
 guest_terminal_present=(folder/'dedicated-worker-terminal.json').is_file(),
 read_only=True,worker_replayed=False,qualified=False,accepted=False)))
'''
base=(here/'inspect_full109_recovery_via_openssh.py').read_text()
anchor="    assert not (ROOT/'launch-once.json').exists() and SSH.is_file() and KEY.is_file()"
assert base.count(anchor)==1
base=base.replace(anchor,"    assert SSH.is_file() and KEY.is_file()\n    assert json.loads((ROOT/'launch-once.json').read_bytes())['run']=='cmmsa_a8_output_20261010T110328Z_0d5c26f4'")
start=base.index('            remote = """');end=base.index('            command = ',start)
base=base[:start]+'            remote = '+repr(remote)+'\n'+base[end:]
base=base.replace("'openssh-recovery-inspections'", "'native-progress-inspections-v1'")
target=here/'inspect_full109_native_progress_v1.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(base)
ast.parse(base)
print('Derived exact-owned-run read-only native progress inspection; no worker replay')
