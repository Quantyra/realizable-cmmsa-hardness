import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
stop=json.loads((check/'vm-termination.json').read_bytes())
assert stop['custody_verified_before_stop'] and stop['independent']['status']=='TERMINATED'
assert str(stop['independent']['id'])=='7237681467779354904' and stop['other_vm_modified'] is False
folder=check/'termination-controls'
assert all(c['native_exit']==0 for c in json.loads((folder/'commands.json').read_bytes()))
target=here/'full109-guarded-stop-progress-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[check/'vm-termination.json',here/'terminate_full109_builder02_after_custody.py']
paths+=[p for p in sorted(folder.rglob('*')) if p.is_file()]
for progress in sorted((ROOT/'native-progress-inspections-v1').glob('*')):
 assert (progress/'inspection.json').is_file()
 assert all(c['native_exit']==0 for c in json.loads((progress/'commands.json').read_bytes()))
 paths+=[p for p in sorted(progress.rglob('*')) if p.is_file()]
rows=[]
for i,path in enumerate(paths):
 data=path.read_bytes();dest=target/f'{i:03d}-{path.name}';dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,original_stop_handle=49952,
 tool_native_exit=0,native_custody_before_stop=True,independent_termination=True,
 other_vm_modified=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows))))
