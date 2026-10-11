import hashlib
import json
import sys
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
action,number,handle=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
assert action in ('plan','receipt') and number in range(84,90)
from audit_full109_trace_cache_small_v1 import main as audit
audit(action,number)
derivation=json.loads((here/'full109-trace-small-cache-control-derivation-v1.json').read_bytes())
scope=next(r for r in derivation['scopes'] if r['number']==number)
op_action='plan' if action=='plan' else 'execute'
matches=[]
for path in (ROOT/'consumption-v3/cache-repoint-controls').glob('*/operation.json'):
 op=json.loads(path.read_bytes())
 if op['remote_control']==scope['remote_control'] and op['action']==op_action:matches.append(path.parent)
assert len(matches)==1
folder=matches[0]
assert all(c['native_exit']==0 for c in json.loads((folder/'commands.json').read_bytes()))
target=here/f'full109-trace-small-{action}-native{number}-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[p for p in sorted(folder.rglob('*')) if p.is_file()]
paths.append(ROOT/'consumption-v3'/f'cache-small-{action}-audit-native{number}-v1.json')
rows=[]
for i,path in enumerate(paths):
 data=path.read_bytes();dest=target/f'{i:03d}-{path.name}';dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,original_tool_handle=handle,native_exit=0,
 complete_current_row_audit=True,trace_executed=False),indent=2)+'\n')
print(json.dumps(dict(number=number,action=action,files=len(rows))))
