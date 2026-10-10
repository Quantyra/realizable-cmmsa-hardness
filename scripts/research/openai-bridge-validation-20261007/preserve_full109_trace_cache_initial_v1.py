import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent;trace=ROOT/'consumption-v3'
folders=[trace/'cache-repoint-controls/20261010T114131997702Z',trace/'cache-repoint-controls/20261010T114132016791Z',
 ROOT/'trace-resource-inspections-v1/20261010T113744781862Z',trace/'idle-refresh-controls/20261010T114109709325Z']
assert not (trace/'launch-once.json').exists()
target=here/'full109-trace-cache-initial-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[p for folder in folders for p in sorted(folder.rglob('*')) if p.is_file()]
paths.append(trace/'cache-large-plan-audit-native109-v2.json')
rows=[]
for i,path in enumerate(paths):
 data=path.read_bytes();dest=target/f'{i:03d}-{path.name}';dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,plan_handles={107:86131,109:20476},
 plan109_complete_rows=9666,plan107_native_exit=1,cache_recovery_executed=False,trace_executed=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows))))
