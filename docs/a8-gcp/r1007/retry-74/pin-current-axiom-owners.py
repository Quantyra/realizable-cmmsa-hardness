"""Pin current owner bytes separately from preserved historical name mapping."""
import json,hashlib,re
from pathlib import Path
p=Path(__file__).resolve().parent; cap=p.parent/'captures/capture-full-a22-hc46-74'
manifest=json.loads((cap/'manifest.json').read_bytes())
old=json.loads((p/'axiom-declaration-owner-map.json').read_bytes())
rows=[]
for row in old['requests']:
    owner=row['owner_file']; data=(cap/'inputs'/owner).read_bytes()
    digest=hashlib.sha256(data).hexdigest().upper()
    assert digest==manifest['project_sources'][owner]['sha256']
    short=row['qualified'].rsplit('.',1)[1]
    lines=[i+1 for i,line in enumerate(data.decode('utf-8').splitlines()) if re.search(r'\b(?:theorem|def|abbrev|lemma)\s+'+re.escape(short)+r'\b',line)]
    assert len(lines)==1,(owner,short,lines)
    rows.append({'qualified':row['qualified'],'original_request':row['original_request'],'owner_file':owner,'current_capture_sha256':digest,'current_owner_line':lines[0]})
value={'capture':'capture-full-a22-hc46-74','manifest_sha256':hashlib.sha256((cap/'manifest.json').read_bytes()).hexdigest().upper(),'historical_owner_map_preserved':True,'historical_owner_map_sha256':hashlib.sha256((p/'axiom-declaration-owner-map.json').read_bytes()).hexdigest().upper(),'requests':rows,'acceptance':False}
with (p/'current-axiom-owner-identities.json').open('x',encoding='utf-8') as f:json.dump(value,f,indent=2)
print(json.dumps({'requests':len(rows),'current_capture':value['capture'],'historical_mapping_preserved':True}))
