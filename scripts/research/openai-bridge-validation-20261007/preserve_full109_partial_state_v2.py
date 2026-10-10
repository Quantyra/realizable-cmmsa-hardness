import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
source=ROOT/'openssh-partial-inspections-v2/20261010T102820618094Z'
value=json.loads((source/'inspection.json').read_bytes())
assert value['verified_completed_rows']==18781 and value['remaining_rows']==452
assert value['all_row_states_verified'] and not value['boundary_backups_present']
assert all(c['native_exit']==0 for c in json.loads((source/'commands.json').read_bytes()))
target=here/'full109-partial-state-record-v2';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
rows=[]
for path in sorted(source.rglob('*')):
 if not path.is_file():continue
 relative=path.relative_to(source);dest=target/relative;dest.parent.mkdir(parents=True,exist_ok=True)
 data=path.read_bytes();dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=relative.as_posix(),bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,original_execute_replayed=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),completed=18781,remaining=452)))
