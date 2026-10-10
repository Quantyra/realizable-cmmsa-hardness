import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
qualified=check/'qualified-native';report=qualified/marker['run']/'material-expanded-native-report.json'
value=json.loads(report.read_bytes())
assert value['full109_expanded_native_gates_green'] and value['project_closure_sources']==348
assert value['expanded_requested_axiom_count']==261 and value['cache_objects_unchanged']==566
assert value['owned_warning_headers']==value['inherited_regression_headers']==[0]*7
control=ROOT/'qualification-controls/after-independent-termination-v1'
command=json.loads((control/'command.json').read_bytes());assert command['native_exit']==0
target=here/'full109-qualified-native-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[p for p in sorted(qualified.rglob('*')) if p.is_file()]
paths+=[p for p in sorted(control.rglob('*')) if p.is_file()]
rows=[]
for i,path in enumerate(paths):
 data=path.read_bytes();dest=target/f'{i:03d}-{path.name}';dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,original_tool_handle=79050,
 original_premature_admission_preserved=True,native_qualification_green=True,
 trace_and_body_review_pending=True,accepted=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),report_sha256=hashlib.sha256(report.read_bytes()).hexdigest().upper())))
