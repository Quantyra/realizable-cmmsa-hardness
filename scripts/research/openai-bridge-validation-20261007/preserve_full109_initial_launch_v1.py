import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
marker=ROOT/'launch-once.json';value=json.loads(marker.read_bytes());check=Path(value['preflight'])
assert value['run']=='cmmsa_a8_output_20261010T110328Z_0d5c26f4'
target=here/'full109-initial-launch-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
commands=json.loads((check/'commands.json').read_bytes())
assert len(commands)==3 and all(c['native_exit']==0 for c in commands)
paths=[marker,check/'preflight.json',check/'commands.json']
paths+=sorted((check/'executed-controls').glob('*'))
paths+=sorted((check/'control').glob('*'))
rows=[]
for number,path in enumerate(paths):
 data=path.read_bytes();dest=target/f'{number:03d}-{path.name}';dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,run=value['run'],
 phase='Original prelaunch completed; original worker transport remains live',
 original_tool_handle=70186,terminal_claimed=False,accepted=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),run=value['run'])))
