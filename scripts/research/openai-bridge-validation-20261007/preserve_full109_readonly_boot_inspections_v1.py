"""Preserve completed native boot/inspection/idle records as exact raw bytes."""
import hashlib
import json
from pathlib import Path
import subprocess
from full109_builder02_controller import ROOT

here=Path(__file__).parent
target=here/'full109-readonly-recovery-record-v1'
target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
folders=[ROOT/'readonly-recovery-boot-v1',
 ROOT/'openssh-recovery-inspections/20261010T101641635054Z',
 ROOT/'openssh-recovery-inspections/20261010T102631456962Z',
 ROOT/'idle-refresh-controls/20261010T102701646898Z']
assert json.loads((folders[0]/'boot-result.json').read_bytes())['after']['status']=='RUNNING'
assert json.loads((folders[2]/'inspection.json').read_bytes())['partial_present']
assert json.loads((folders[3]/'idle-refreshed.json').read_bytes())['idle_timer_active']
rows=[]
for number,folder in enumerate(folders):
 for source in sorted(folder.rglob('*')):
  if not source.is_file():continue
  dest=target/str(number)/source.relative_to(folder);dest.parent.mkdir(parents=True,exist_ok=True)
  data=source.read_bytes();dest.open('xb').write(data)
  rows.append(dict(source=str(source),target=dest.relative_to(target).as_posix(),bytes=len(data),
   sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows, compiler_invoked=False,
 original_recovery_replayed=False, termination_cause_unverified=True),indent=2)+'\n')
print(json.dumps(dict(folder=str(target),files=len(rows))))
