"""Bind closeout helpers to assigned run; immutable capture remains unchanged."""
import ast,json
from pathlib import Path
p=Path(__file__).resolve().parent
old='cmmsa_a8_output_20261006T023135Z_1fc1ec5c'
new='cmmsa_a8_output_20261006T030313Z_2f112c58'
oldhash='62798AB2F09939240650412D555E6C5CFC80D82BC7960944F515E310A2E70286'
newhash='975E730DDF65DAB8900DBD0FE1434BD24000CCE43F599013FC47299958527728'
for name in ['finish-native.py','associate-offer.py']:
    f=p/name; text=f.read_text(encoding='utf-8')
    assert old in text
    text=text.replace(old,new).replace(oldhash,newhash)
    ast.parse(text); f.write_bytes(text.encode('utf-8'))
with (p/'run-context.json').open('x',encoding='utf-8') as f:
    json.dump({'run':new,'manifest_sha256':newhash,'immutable_capture_modified':False,'changed_helpers':['finish-native.py','associate-offer.py'],'local_Lean_compilation':False},f,indent=2)
