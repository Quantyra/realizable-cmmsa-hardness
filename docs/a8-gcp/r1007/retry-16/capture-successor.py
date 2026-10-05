"""Snapshot offered author bytes without executing a compiler or Git."""
import hashlib, json, sys
from pathlib import Path
from datetime import datetime, timezone
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
name=sys.argv[1]
assert name.startswith('successor-') and '/' not in name and '\\' not in name
folder=HERE/name; folder.mkdir(exist_ok=False)
rows={}; encoding={}
for offer in sys.argv[2:]:
    filename,expected=offer.split('=',1)
    assert filename.endswith('.lean') and '/' not in filename and '\\' not in filename
    data=(REPO/'lean/PvNP/RealizableHardness'/filename).read_bytes()
    digest=hashlib.sha256(data).hexdigest().upper()
    assert digest==expected,filename
    snapshot=folder/(filename+'.snapshot')
    with snapshot.open('xb') as stream: stream.write(data)
    text=data.decode('utf-8','strict')
    rows[filename]=digest
    encoding[filename]={'UTF8':True,'noBOM':not data.startswith(b'\xef\xbb\xbf'),'replacement_characters':text.count('\ufffd')}
receipt={'utc':datetime.now(timezone.utc).isoformat(),'exact_sha256':rows,'encoding':encoding,'compile_launched':False,'acceptance':False,'helper_credit':0,'live_capture_unchanged':'capture-retry-16','author_released_after_hash_verification':True}
with (folder/'custody.json').open('x',encoding='utf-8',newline='\n') as stream: json.dump(receipt,stream,indent=2)
print(json.dumps(receipt,indent=2))
