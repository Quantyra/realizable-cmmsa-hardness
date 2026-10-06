"""Map diagnostic-only markers/errors to original lines; never imply proof acceptance."""
import json,re,sys,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
run=PACKAGE/'runs'/sys.argv[1]; root=run/'remote-evidence' if len(sys.argv)<3 else run/sys.argv[2]
mapdata=json.loads((HERE/'instrumentation-map.json').read_bytes()); rows=sorted(mapdata['markers'],key=lambda r:r['insertion_before_line'])
positions=[r['insertion_before_line']+i for i,r in enumerate(rows)]
texts=[]
for stream in ['stdout','stderr']:
 path=root/(f'stage-4.{stream}' if len(sys.argv)<3 else f'native-{stream}.snapshot')
 texts.append((stream,path.read_text(encoding='utf-8')))
markers=[]; errors=[]; warnings=[]
for stream,text in texts:
 lines=text.splitlines()
 for i,line in enumerate(lines):
  if line.startswith('CMMSA-A11-BEGIN '): markers.append({'stream':stream,'marker':line})
  match=re.match(r'^(?:error:\s*)?(?:[^ ]*/)?A11MarkedDiagnostic\.lean:(\d+):(\d+):\s*(error|warning):\s*(.*)',line)
  if match:
   n=int(match[1]); end=next((j for j in range(i+1,len(lines)) if lines[j].startswith('CMMSA-A11-BEGIN ') or re.match(r'^(?:[^ ]*/)?A11MarkedDiagnostic\.lean:\d+:\d+:',lines[j])),len(lines))
   value={'stream':stream,'derived_line':n,'original_line':n-sum(x<n for x in positions),'column':int(match[2]),'message':match[4],'exact_block':'\n'.join(lines[i:end])}
   (errors if match[3]=='error' else warnings).append(value)
value={'diagnostic_only':True,'acceptance':False,'markers_record_command_entry_only_not_proof_completion':True,'original_source_sha256':mapdata['original_source_sha256'],'derived_source_sha256':mapdata['derived_sha256'],'instrumentation_map_sha256':hashlib.sha256((HERE/'instrumentation-map.json').read_bytes()).hexdigest().upper(),'markers':markers,'last_observed_marker':markers[-1] if markers else None,'derived_error_headers':len(errors),'derived_warning_headers':len(warnings),'errors':errors,'warnings':warnings,'actual_original_standard_gates_still_required':[5,6,7]}
output=run/'marked-diagnostic-report.json' if len(sys.argv)<3 else root/'marked-diagnostic-summary.json'
with output.open('x',encoding='utf-8') as f: json.dump(value,f,indent=2)
print(json.dumps({k:v for k,v in value.items() if k not in ['markers','errors','warnings']},indent=2))
