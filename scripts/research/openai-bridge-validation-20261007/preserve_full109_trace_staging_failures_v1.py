import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
trace=ROOT/'consumption-v3'
folders=[trace/'staging-controls/20261010T112816378308Z',trace/'staging-controls/20261010T113523127766Z']
first=json.loads((folders[0]/'commands.json').read_bytes())
second=json.loads((folders[1]/'commands.json').read_bytes())
assert len(first)==5 and [r['native_exit'] for r in first]==[0,0,0,0,1]
assert first[2]['argv'][1:4]==['compute','instances','start']
assert len(second)==7 and [r['native_exit'] for r in second]==[0,0,0,0,0,0,1]
assert not any(r['argv'][1:4]==['compute','instances','start'] for r in second)
assert 'Insufficient remote storage' in (folders[1]/'6.stderr').read_text()
assert not (trace/'launch-once.json').exists()
target=here/'full109-trace-staging-failures-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[p for folder in folders for p in sorted(folder.rglob('*')) if p.is_file()]
paths+=[trace/'green-binding.json',here/'stage_full109_consumption_v3.py']
rows=[]
for i,path in enumerate(paths):
 data=path.read_bytes();dest=target/f'{i:03d}-{path.name}';dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,original_handles=[69730,81809],
 original_vm_start_count=1,probe_executed=False,scope_reduced=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows))))
