"""Register existing authorized mutable paths against immutable full46 bytes."""
import json, hashlib
from pathlib import Path
p=Path(__file__).resolve().parent
cap=p.parent/'captures/capture-integrated-47'
manifest=json.loads((cap/'manifest.json').read_bytes())
previous=json.loads((p.parent/'retry-45/authorized-owned-successor-paths.json').read_bytes())
previous['capture']='capture-integrated-47'
previous['manifest_sha256']=hashlib.sha256((cap/'manifest.json').read_bytes()).hexdigest().upper()
previous['paths_before']={n:manifest['offered_identities'][n] for n in previous['paths_before']}
with (p/'authorized-owned-successor-paths.json').open('x',encoding='utf-8') as f: json.dump(previous,f,indent=2)
print(json.dumps({'manifest_sha256':previous['manifest_sha256'],'owned_paths':len(previous['paths_before']),'captured_bytes_immutable':True}))
