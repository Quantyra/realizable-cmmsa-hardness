"""Bind closeout helpers to exact assigned full48 run; capture untouched."""
import ast,json
from pathlib import Path
p=Path(__file__).resolve().parent
old='cmmsa_a8_output_20261006T031832Z_31df8fff'; new='cmmsa_a8_output_20261006T033338Z_dd58a400'
oldhash='94671F5330D2A6F570A575559E627A6BF179A7B45BCF97AE3E4AE90BA05D65F4'
newhash='442B80877B79DBA15AF42479C66EA547DF97A1F21FB2A141A52C10F28577B1C3'
for name in ['finish-native.py','associate-offer.py']:
    f=p/name; text=f.read_text(encoding='utf-8'); assert old in text
    text=text.replace(old,new).replace(oldhash,newhash)
    ast.parse(text); f.write_bytes(text.encode('utf-8'))
with (p/'run-context.json').open('x',encoding='utf-8') as f:json.dump({'run':new,'manifest_sha256':newhash,'immutable_capture_modified':False,'local_Lean_compilation':False},f,indent=2)
