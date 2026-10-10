import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent;trace=ROOT/'consumption-v3'
folders=[trace/'cache-repoint-controls/20261010T115559939885Z',ROOT/'trace-cache-allocation-inspections-v1/20261010T115056168593Z',
 trace/'idle-refresh-controls/20261010T115602141288Z']
failures=[]
for folder in (trace/'cache-repoint-controls').glob('20261010T171948*'):
 commands=json.loads((folder/'commands.json').read_bytes());assert len(commands)==1 and commands[0]['native_exit']==0
 state=json.loads((folder/'control/000.stdout').read_bytes());assert state['status']=='TERMINATED' and str(state['id'])=='7237681467779354904'
 failures.append(folder)
assert len(failures)==6
folders+=sorted(failures)
target=here/'full109-trace-recovery-checkpoint-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[p for f in folders for p in sorted(f.rglob('*')) if p.is_file()]
paths.append(trace/'cache-large-receipt-audit-native109-v2.json')
rows=[]
for i,path in enumerate(paths):
 data=path.read_bytes();dest=target/f'{i:03d}-{path.name}';dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,large_execution_handle=13614,large_native_exit=0,
 inventory_handle=59714,small_admission_handles=[60119,17809,26831,58764,89534,17137],
 small_remote_plan_invoked=False,trace_executed=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows))))
