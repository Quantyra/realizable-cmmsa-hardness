import hashlib
import json
from full109_builder02_controller import ROOT
from pathlib import Path
here=Path(__file__).parent
source=ROOT/'scope3-remaining-only-controls-v1/20261010T103230099538Z'
target=here/'full109-scope3-continuation-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[p for p in sorted(source.rglob('*')) if p.is_file()]
paths.append(ROOT/'storage-receipt-complete-audit-v3-remaining-only-v1.json')
rows=[]
for i,path in enumerate(paths):
 dest=target/f'{i:03d}-{path.name}';data=path.read_bytes();dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,original_execute_replayed=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows))))
