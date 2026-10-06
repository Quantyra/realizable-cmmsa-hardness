"""Bind offline closeout helpers to the assigned full47 run."""
import ast,json
from pathlib import Path
p=Path(__file__).resolve().parent
old='cmmsa_a8_output_20261006T030313Z_2f112c58'; new='cmmsa_a8_output_20261006T031832Z_31df8fff'
oldhash='975E730DDF65DAB8900DBD0FE1434BD24000CCE43F599013FC47299958527728'
newhash='94671F5330D2A6F570A575559E627A6BF179A7B45BCF97AE3E4AE90BA05D65F4'
for name in ['finish-native.py','associate-offer.py']:
    f=p/name; text=f.read_text(encoding='utf-8'); assert old in text
    text=text.replace(old,new).replace(oldhash,newhash)
    ast.parse(text); f.write_bytes(text.encode('utf-8'))
with (p/'run-context.json').open('x',encoding='utf-8') as f:json.dump({'run':new,'manifest_sha256':newhash,'immutable_capture_modified':False,'local_Lean_compilation':False},f,indent=2)
