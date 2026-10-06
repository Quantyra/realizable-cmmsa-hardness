"""Add current-live context without rewriting original offered-byte receipts."""
import json,sys,hashlib
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
name=sys.argv[1]
assert name.startswith('successor-') and '/' not in name and '\\' not in name
folder=PACKAGE/'retry-16'/name
custody=json.loads((folder/'custody.json').read_bytes())
manifest=json.loads((PACKAGE/'captures/capture-integrated-41/manifest.json').read_bytes())
source_paths=['lean/PvNP/RealizableHardness/'+p.name.removesuffix('.snapshot') for p in folder.glob('*.lean.snapshot')]
context={'utc':datetime.now(timezone.utc).isoformat(),'original_custody_sha256':hashlib.sha256((folder/'custody.json').read_bytes()).hexdigest().upper(),'original_receipt_preserved':True,'current_capture':'capture-integrated-41','current_manifest_sha256':'0A970843040C54A751789DB745DF9529491072DA538482D9A92A52432CD1F198','current_run':'cmmsa_a8_output_20261006T013137Z_19165dbb','source_paths':source_paths,'source_paths_excluded_current_closure':all(n not in manifest['project_sources'] for n in source_paths),'new_compiler_started':False,'source_only':True,'acceptance':False,'authorization_context':'retry-41/authorized-owned-successor-paths.json for A11; captured A8 authors released after immutable capture ACK'}
with (folder/'current-live-context.json').open('x',encoding='utf-8',newline='\n') as stream: json.dump(context,stream,indent=2)
print(json.dumps(context,indent=2))
