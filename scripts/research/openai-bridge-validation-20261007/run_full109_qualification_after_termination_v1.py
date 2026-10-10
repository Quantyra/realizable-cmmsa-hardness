"""Capture complete original audit output only after independent termination."""
from datetime import datetime,timezone
import json
from pathlib import Path
import subprocess
import sys
from full109_builder02_controller import ROOT
from custody_checks import digest
here=Path(__file__).parent
marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
stop=json.loads((check/'vm-termination.json').read_bytes())
assert stop['run']==marker['run'] and stop['custody_verified_before_stop']
assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
source=here/'full109_native_audit.py'
assert digest(source)==marker['extra_local_controls'][source.name]
report=check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
assert not report.exists()
folder=ROOT/'qualification-controls/after-independent-termination-v1';folder.mkdir(parents=True,exist_ok=False)
argv=[sys.executable,'-B','-X','utf8',str(source)]
record=dict(argv=argv,control_sha256=digest(source),started_utc=datetime.now(timezone.utc).isoformat(),
 original_failed_admission_handle=37825,independent_termination_verified=True)
(folder/'command.json').write_text(json.dumps(record,indent=2)+'\n')
with (folder/'stdout').open('xb') as out,(folder/'stderr').open('xb') as err:
    process=subprocess.Popen(argv,stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW)
    while True:
        try:code=process.wait(timeout=30);break
        except subprocess.TimeoutExpired:print('Original qualification remains active',process.pid,flush=True)
record.update(native_exit=code,finished_utc=datetime.now(timezone.utc).isoformat(),
 stdout_sha256=digest(folder/'stdout'),stderr_sha256=digest(folder/'stderr'))
(folder/'command.json').write_text(json.dumps(record,indent=2)+'\n')
if code:print(json.dumps(dict(folder=str(folder),native_exit=code)),flush=True);raise SystemExit(code)
qualified=json.loads(report.read_bytes())
print(json.dumps(dict(folder=str(folder),report_sha256=digest(report),
 full109_expanded_native_gates_green=qualified['full109_expanded_native_gates_green'],
 project_sources=qualified['project_closure_sources'],requested_axioms=qualified['expanded_requested_axiom_count'],
 owned_warning_headers=qualified['owned_warning_headers'],accepted=qualified['accepted'])),flush=True)
