import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
here=Path(__file__).parent
source=ROOT/'existing-staging-resume-controls/20261010T110030352311Z'
receipt=json.loads((source/'verified-existing-stage.json').read_bytes())
assert receipt['preflight']['project_sources_verified']==348
assert receipt['preflight']['disk_available_bytes']>=40*1024**3
assert receipt['preflight']['available_memory_bytes']>=48*1024**3
assert all(c['native_exit']==0 for c in json.loads((source/'commands.json').read_bytes()))
target=here/'full109-existing-stage-v4-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[p for p in sorted(source.rglob('*')) if p.is_file()]
paths+=[here/'resume_full109_staging_after_storage_v4.py',here/'full109_verify_existing.py']
rows=[]
for i,path in enumerate(paths):
 dest=target/f'{i:03d}-{path.name}';data=path.read_bytes();dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,compiler_invoked=False,
 full_scope_existing_stage_verified=True),indent=2)+'\n')
print(json.dumps(dict(files=len(rows))))
