"""Add current-live context without rewriting original offered-byte receipts."""
import json,sys,hashlib
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
name=sys.argv[1]
assert name.startswith('successor-') and '/' not in name and '\\' not in name
folder=PACKAGE/'retry-16'/name
custody=json.loads((folder/'custody.json').read_bytes())
manifest=json.loads((PACKAGE/'captures/capture-integrated-21/manifest.json').read_bytes())
source_paths=['lean/PvNP/RealizableHardness/'+p.name.removesuffix('.snapshot') for p in folder.glob('*.lean.snapshot')]
context={'utc':datetime.now(timezone.utc).isoformat(),'original_custody_sha256':hashlib.sha256((folder/'custody.json').read_bytes()).hexdigest().upper(),'original_receipt_preserved':True,'current_capture':'capture-integrated-21','current_manifest_sha256':'FB7A0045CB220F42C40FD73A35A1CC40E1A5FB49B743BED3872FEAFD7164E77E','current_run':'cmmsa_a8_output_20261005T205338Z_98887da0','source_paths':source_paths,'source_paths_excluded_current_closure':all(n not in manifest['project_sources'] for n in source_paths),'new_compiler_started':False,'source_only':True,'acceptance':False,'authorization_context':'retry-21/authorized-owned-successor-paths.json for A11; captured A8 authors released after immutable capture ACK'}
with (folder/'current-live-context.json').open('x',encoding='utf-8',newline='\n') as stream: json.dump(context,stream,indent=2)
print(json.dumps(context,indent=2))
