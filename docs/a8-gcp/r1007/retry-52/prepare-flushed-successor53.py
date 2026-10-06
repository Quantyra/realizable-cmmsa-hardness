"""Prepare successor only after preserved51 TERM; diagnostic stream control is separate."""
from pathlib import Path
import json,ast,hashlib
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
run=PACKAGE/'runs/cmmsa_a8_output_20261006T070048Z_e95389af'
terminal=json.loads((run/'terminal.json').read_bytes()); assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
custody=json.loads((run/'custody.json').read_bytes())
assert hashlib.sha256(Path(custody['repository_path']).read_bytes()).hexdigest().upper()==custody['remote_sha256']
dst=PACKAGE/'retry-53'; dst.mkdir(exist_ok=False)
allowed=['controller.py','finish-native.py','associate-offer.py','check-authorized-preservation.py','compare-native.py','full-original-a8-native-gates.py','pin-current-axiom-owners.py','register-captured-successors.py','axiom-declaration-owner-map.json','accepted-a9-source.lean.snapshot','accepted-a9-dependency.json','fetch-profile-live.py','observe-current-stage.py','evaluate-marked-diagnostic.py']
for n in allowed:
 data=(HERE/n).read_bytes()
 if n.endswith('.py'): data=data.replace(b'retry-52',b'retry-53').replace(b'capture-integrated-52',b'capture-integrated-53').replace(b'integrated52_import',b'integrated53_import').replace(b'finish52_import',b'finish53_import')
 (dst/n).write_bytes(data)
s=(PACKAGE/'retry-50/prepare-marked-successor51.py').read_text()
s=s.replace('cmmsa_a8_output_20261006T055942Z_3a1927c5',run.name).replace('successor-native-50-a11-repair','successor-native-52-a11-partition-repair').replace('E461EF54E25C41658EB5AE3ECB19912B55412085DD10688BD9772F5122B16CD3','700F8DA70D5F148A640EA389F911C045A45E2256E98A3BDB5B9C59FF17EA7B68').replace('retry-52/derived-marked-diagnostic','retry-53/derived-marked-diagnostic')
old="marker=('#eval IO.eprintln '+json.dumps(label,ensure_ascii=True)+'\\n').encode()"
new="marker=('#eval (do let markerStream ← IO.getStderr; markerStream.putStrLn '+json.dumps(label,ensure_ascii=True)+'; markerStream.flush : IO Unit)\\n').encode()"
assert old in s; s=s.replace(old,new)
s=s.replace("x.startswith(b'#eval IO.eprintln \"CMMSA-A11-BEGIN ')","x.startswith(b'#eval (do let markerStream ')")
assert 'stripped==data' in s
f=dst/'derive-flushed-markers.py'; f.write_text(s,encoding='utf-8'); ast.parse(s)
exec(compile(s,str(f),'exec'),{'__file__':str((PACKAGE/'retry-50/prepare-marked-successor51.py').resolve()),'__name__':'__main__'})
data=(dst/'derived-marked-diagnostic/A11MarkedDiagnostic.lean').read_bytes(); mapdata=(dst/'derived-marked-diagnostic/instrumentation-map.json').read_bytes(); ident=json.loads(mapdata)
(dst/'marked-diagnostic.lean.snapshot').write_bytes(data); (dst/'instrumentation-map.json').write_bytes(mapdata)
identity={'file':'A11MarkedDiagnostic.lean','sha256':hashlib.sha256(data).hexdigest().upper(),'instrumentation_map_sha256':hashlib.sha256(mapdata).hexdigest().upper(),'original_source_sha256':ident['original_source_sha256'],'exact_original_bytes_after_marker_removal':True,'diagnostic_only':True,'acceptance':False,'native_output_channel':'stderr','per_marker_flush':True,'diagnostic_cli_options':['-DstderrAsMessages=false']}
(dst/'diagnostic-artifact-identity.json').write_text(json.dumps(identity,indent=2))
f=dst/'controller.py'; t=f.read_text(); old="['lake','env','lean','A11MarkedDiagnostic.lean']"; new="['lake','env','lean','-DstderrAsMessages=false','A11MarkedDiagnostic.lean']"; assert new in t; f.write_text(t,encoding='utf-8')
(dst/'author-report.md').write_text('Full original215/14/49 scope; actual700F8DA7/F981 proof-only successor. Eightstages: originalA8 gates0-3, separatelypinned bounded900s derivedmarker diagnostic4 with documented stderrAsMessages=false ONLY for diagnosticstream and explicitStream.flush permarker, standardactualA11 source5/Checks6/freshall49gate7. Original in-file options/imports/proofs/hypotheses remain exact aftermarkerremoval; derivedmarkers/CLIstreamcontrol supply no acceptance ororiginalowner/requestcredit. Same70min resource/custody/cache400/inherited/warning gates. No localLean.\n')
for f in dst.glob('*.py'): ast.parse(f.read_text(encoding='utf-8-sig'))
print(json.dumps({'future':'retry-53','diagnostic':identity,'markers':len(ident['markers']),'compile_started':False},indent=2))
