"""Derive markers only after original run custody/termination. Never edit actual A11."""
from pathlib import Path
import re,json,hashlib
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
run=PACKAGE/'runs/cmmsa_a8_output_20261006T055942Z_3a1927c5'
terminal=json.loads((run/'terminal.json').read_bytes()); assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
custody=json.loads((run/'custody.json').read_bytes())
for k in ['short_path','repository_path']:
 assert hashlib.sha256(Path(custody[k]).read_bytes()).hexdigest().upper()==custody['remote_sha256']
source=PACKAGE/'captures/capture-integrated-50/inputs/lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A11WeightedAggregate.lean'
data=source.read_bytes(); assert hashlib.sha256(data).hexdigest().upper()=='D650DDCDACFC3DEE754275147038F69F2CA9D774530DF89BDCFF196117F0FFD0'
lines=data.splitlines(keepends=True); text=[x.decode('utf-8') for x in lines]
pattern=re.compile(r'^(?:(?:private|protected|noncomputable) )*(?:theorem|lemma|def|abbrev|structure|inductive)\b|^(?:namespace|section|end|variable|open|set_option|noncomputable section)\b')
markers={}; rows=[]
for i,line in enumerate(text):
 if not pattern.match(line): continue
 start=i
 # Keep leading doc/block comments and attributes attached to their command.
 while start>0:
  previous=text[start-1].strip()
  if not previous: start-=1; continue
  if previous.startswith('@[') or (previous.startswith('set_option ') and previous.endswith(' in')): start-=1; continue
  if previous.endswith('-/'):
   j=start-1
   while j>=0 and '/-' not in text[j]: j-=1
   assert j>=0; start=j; continue
  break
 assert start not in markers,(start,i)
 label='CMMSA-A11-BEGIN original-line='+str(i+1)+' command='+line.strip().replace('"','')
 marker=('#eval IO.eprintln '+json.dumps(label,ensure_ascii=True)+'\n').encode()
 markers[start]=marker; rows.append({'original_line':i+1,'insertion_before_line':start+1,'command':line.strip(),'marker':label})
output=b''.join(markers.get(i,b'')+line for i,line in enumerate(lines))
stripped=b''.join(x for x in output.splitlines(keepends=True) if not x.startswith(b'#eval IO.eprintln "CMMSA-A11-BEGIN '))
assert stripped==data
out=HERE/'derived-marked-diagnostic'; out.mkdir(exist_ok=False)
(out/'A11MarkedDiagnostic.lean').write_bytes(output)
(out/'instrumentation-map.json').write_text(json.dumps({'original_source_sha256':hashlib.sha256(data).hexdigest().upper(),'derived_sha256':hashlib.sha256(output).hexdigest().upper(),'exact_original_bytes_after_marker_removal':True,'markers':rows,'acceptance':False,'imports_options_hypotheses_proof_body_unchanged':True,'original_run_custody_sha256':custody['remote_sha256']},indent=2))
print(json.dumps({'markers':len(rows),'derived_source_only':True,'no_compile':True}))
