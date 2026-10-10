from pathlib import Path
import json
import hashlib
from full109_builder02_controller import ROOT
here=Path(__file__).parent
target=here/'full109-scope7-failed-transport-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
folders=[ROOT/'cache-repoint-controls/20261010T093457641991Z',
 ROOT/'scope7-local-orphan-transport-observation-v1',ROOT/'idle-refresh-controls/20261010T103802346576Z']
commands=json.loads((folders[0]/'commands.json').read_bytes())
assert len(commands)==7 and commands[-1]['native_exit']==1
rows=[]
for i,folder in enumerate(folders):
 for source in sorted(folder.rglob('*')):
  if not source.is_file():continue
  dest=target/str(i)/source.relative_to(folder);dest.parent.mkdir(parents=True,exist_ok=True)
  data=source.read_bytes();dest.open('xb').write(data)
  rows.append(dict(source=str(source),target=dest.relative_to(target).as_posix(),bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,original_transfer_native_exit=1,
 disconnected_local_proxy_cancelled=True,planner_replayed=False,compiler_invoked=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows))))
