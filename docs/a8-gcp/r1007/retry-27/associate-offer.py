"""Add current-live context without rewriting original offered-byte receipts."""
import json,sys,hashlib
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
name=sys.argv[1]
assert name.startswith('successor-') and '/' not in name and '\\' not in name
folder=PACKAGE/'retry-16'/name
custody=json.loads((folder/'custody.json').read_bytes())
manifest=json.loads((PACKAGE/'captures/capture-integrated-27/manifest.json').read_bytes())
source_paths=['lean/PvNP/RealizableHardness/'+p.name.removesuffix('.snapshot') for p in folder.glob('*.lean.snapshot')]
context={'utc':datetime.now(timezone.utc).isoformat(),'original_custody_sha256':hashlib.sha256((folder/'custody.json').read_bytes()).hexdigest().upper(),'original_receipt_preserved':True,'current_capture':'capture-integrated-27','current_manifest_sha256':'33A8D59FC8AB9CC0646C1B67035EFB3C7100434806343AD64111CF66DAF654BD','current_run':'cmmsa_a8_output_20261005T221636Z_a6585fa9','source_paths':source_paths,'source_paths_excluded_current_closure':all(n not in manifest['project_sources'] for n in source_paths),'new_compiler_started':False,'source_only':True,'acceptance':False,'authorization_context':'retry-27/authorized-owned-successor-paths.json for A11; captured A8 authors released after immutable capture ACK'}
with (folder/'current-live-context.json').open('x',encoding='utf-8',newline='\n') as stream: json.dump(context,stream,indent=2)
print(json.dumps(context,indent=2))
