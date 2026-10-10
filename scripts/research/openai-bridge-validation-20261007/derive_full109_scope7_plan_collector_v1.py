from pathlib import Path
import hashlib
import ast
here=Path(__file__).parent
source_sha=hashlib.sha256((here/'full109_storage_cache_repoint_v7.py').read_bytes()).hexdigest().upper()
remote='''import base64,hashlib,json,urllib.request
from pathlib import Path
o=urllib.request.build_opener(urllib.request.ProxyHandler({}))
r=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with o.open(r,timeout=10) as s:
 assert s.headers.get('Metadata-Flavor')=='Google' and s.read().decode()=='7237681467779354904'
home=Path('/home/dfredriksen_quantyra_org');assert Path.home().resolve()==home
folder=home/'full109-storage-cache-repoint-v7'
assert not (folder/'execute-once.json').exists()
assert hashlib.sha256((folder/'full109_storage_cache_repoint_v7.py').read_bytes()).hexdigest().upper()==SOURCE_SHA
data=(folder/'plan.json').read_bytes();pin=hashlib.sha256(data).hexdigest().upper()
assert pin=='E415E10CB486DD5ED253A55B1BEC45F2D9FF29B737C406E7299FF5128ED850DC'
print(json.dumps(dict(plan_sha256=pin,raw_plan_base64=base64.b64encode(data).decode(),read_only=True,planner_replayed=False,compiler_invoked=False)))
'''.replace('SOURCE_SHA',repr(source_sha))
base=(here/'inspect_full109_recovery_via_openssh.py').read_text()
start=base.index('            remote = """');end=base.index('            command = ',start)
base=base[:start]+'            remote = '+repr(remote)+'\n'+base[end:]
base=base.replace("'openssh-recovery-inspections'", "'scope7-readonly-plan-collection-v1'")
base=base.replace('inspection=result, host_key_fingerprint=fingerprint','inspection={k:v for k,v in result.items() if k != "raw_plan_base64"}, host_key_fingerprint=fingerprint')
target=here/'collect_full109_scope7_plan_via_openssh_v1.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(base)
ast.parse(base)
print('Derived read-only collection of existing plan; no planner invocation')
