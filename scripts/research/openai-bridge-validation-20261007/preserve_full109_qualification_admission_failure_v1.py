import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
source=check/'executed-controls/full109_native_audit.py'
assert source.read_bytes()==(here/'full109_native_audit.py').read_bytes()
report=check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
assert not report.exists()
target=here/'full109-qualification-admission-failure-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
data=source.read_bytes();(target/source.name).open('xb').write(data)
observation=dict(schema='full109-qualification-prerequisite-admission-observation-v1',
 original_tool_handle=37825,tool_native_exit=1,run=marker['run'],
 exception='FileNotFoundError: vm-termination.json was not yet available',
 expected_prerequisite=str(check/'vm-termination.json'),qualification_report_created=False,
 full_audit_not_performed=True,compiler_replayed=False,original_tool_output_truncated=True,
 complete_raw_stdout_not_reconstructed=True,accepted=False)
payload=(json.dumps(observation,indent=2)+'\n').encode()
(target/'observation.json').open('xb').write(payload)
rows=[dict(source=str(source),target=source.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()),
 dict(source='Structured observation of original tool result; not raw stdout',target='observation.json',bytes=len(payload),sha256=hashlib.sha256(payload).hexdigest().upper())]
(target/'index.json').write_text(json.dumps(dict(records=rows),indent=2)+'\n')
print(json.dumps(dict(failed_admission_preserved=True,qualification_report_created=False)))
