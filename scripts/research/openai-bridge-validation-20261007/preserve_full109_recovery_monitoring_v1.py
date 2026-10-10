import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
folders=sorted((ROOT/'concurrent-recovery-progress-inspections-v1').glob('*'))
folders+=sorted(p for p in (ROOT/'idle-refresh-controls').glob('*') if p.name>='20261010T104208205265Z')
folders+=sorted((ROOT/'recovery-idle-keeper-controls-v1').glob('*'))
target=here/'full109-recovery-monitoring-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
rows=[]
for number,folder in enumerate(folders):
 assert (folder/'inspection.json').exists() or (folder/'idle-refreshed.json').exists()
 assert all(c['native_exit']==0 for c in json.loads((folder/'commands.json').read_bytes()))
 for source in sorted(folder.rglob('*')):
  if not source.is_file():continue
  dest=target/str(number)/source.relative_to(folder);dest.parent.mkdir(parents=True,exist_ok=True)
  data=source.read_bytes();dest.open('xb').write(data)
  rows.append(dict(source=str(source),target=dest.relative_to(target).as_posix(),bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,snapshot_not_launch_clearance=True,
 idle_timer_remained_enabled=True,compiler_invoked=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),folders=len(folders))))
