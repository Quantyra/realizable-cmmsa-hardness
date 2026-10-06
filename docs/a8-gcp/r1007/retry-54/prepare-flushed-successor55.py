from pathlib import Path
import json,hashlib,ast
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
run=PACKAGE/'runs/cmmsa_a8_output_20261006T074455Z_fd14cccb'
terminal=json.loads((run/'terminal.json').read_bytes()); assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
custody=json.loads((run/'custody.json').read_bytes()); assert hashlib.sha256(Path(custody['repository_path']).read_bytes()).hexdigest().upper()==custody['remote_sha256']
dst=PACKAGE/'retry-55'; dst.mkdir(exist_ok=False)
allowed=['controller.py','finish-native.py','associate-offer.py','check-authorized-preservation.py','compare-native.py','full-original-a8-native-gates.py','pin-current-axiom-owners.py','register-captured-successors.py','axiom-declaration-owner-map.json','accepted-a9-source.lean.snapshot','accepted-a9-dependency.json','fetch-profile-live.py','observe-current-stage.py','evaluate-marked-diagnostic.py']
for n in allowed:
 data=(HERE/n).read_bytes()
 if n.endswith('.py'): data=data.replace(b'retry-54',b'retry-55').replace(b'capture-integrated-54',b'capture-integrated-55').replace(b'integrated54_import',b'integrated55_import').replace(b'finish54_import',b'finish55_import')
 (dst/n).write_bytes(data)
s=(HERE/'derive-flushed-markers.py').read_text(encoding='utf-8').replace('cmmsa_a8_output_20261006T073042Z_6298be2c',run.name).replace('successor-native-53-a11-two-goal-repair','successor-native-54-a11-forward-repair').replace('7238E1BF28632B24774CA6D4AED105D629E235BBC018E7EB04EA4E0525096EF8','5B3406F4B1B2D8FE6977CB265DEBEBFE25D9DA7BF65344FCBF9ABEADE4F91AA0').replace('retry-54/derived-marked-diagnostic','retry-55/derived-marked-diagnostic')
f=dst/'derive-flushed-markers.py'; f.write_bytes(s.encode('utf-8')); ast.parse(s)
exec(compile(s,str(f),'exec'),{'__file__':str((PACKAGE/'retry-50/prepare-marked-successor51.py').resolve()),'__name__':'__main__'})
data=(dst/'derived-marked-diagnostic/A11MarkedDiagnostic.lean').read_bytes(); mapdata=(dst/'derived-marked-diagnostic/instrumentation-map.json').read_bytes(); ident=json.loads(mapdata)
(dst/'marked-diagnostic.lean.snapshot').write_bytes(data); (dst/'instrumentation-map.json').write_bytes(mapdata)
identity={'file':'A11MarkedDiagnostic.lean','sha256':hashlib.sha256(data).hexdigest().upper(),'instrumentation_map_sha256':hashlib.sha256(mapdata).hexdigest().upper(),'original_source_sha256':ident['original_source_sha256'],'exact_original_bytes_after_marker_removal':True,'diagnostic_only':True,'acceptance':False,'native_output_channel':'stderr','per_marker_flush':True,'diagnostic_cli_options':['-DstderrAsMessages=false']}
(dst/'diagnostic-artifact-identity.json').write_text(json.dumps(identity,indent=2),encoding='utf-8')
(dst/'author-report.md').write_text('Full original215/14/49 eightstages; actual5B3406/F981 boundedforwardprojection proofrepair, separate108flushedstderrmarkerdiagnostic with exactmarker-removal bodyidentity, standardactualsource/Checks/all49mandatory. No acceptancefromdiagnostic. Cache400/inherited/resource/warning/custody gates unchanged. No localLean/cleanup.\n',encoding='utf-8')
for f in dst.glob('*.py'): ast.parse(f.read_text(encoding='utf-8'))
print(json.dumps(identity,indent=2))
