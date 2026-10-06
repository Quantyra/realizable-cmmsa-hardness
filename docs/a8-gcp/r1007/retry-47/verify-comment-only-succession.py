"""Prove exact reviewed suffix/import identity; do not infer new native success."""
import json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent; repo=p.parents[3]
cap=p.parent/'captures/capture-integrated-46/inputs'
names=['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8AveragedTransport.lean','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8AveragedAssembly.lean']
rows={}
for name in names:
    old=(cap/name).read_bytes(); new=(repo/name).read_bytes()
    a=old.index(b'/-!'); b=new.index(b'/-!')
    assert old[:a]==new[:b]
    oa=old.index(b'-/',a)+2; nb=new.index(b'-/',b)+2
    assert old[oa:]==new[nb:]
    rows[name]={'reviewed46_sha256':hashlib.sha256(old).hexdigest().upper(),'current_sha256':hashlib.sha256(new).hexdigest().upper(),'imports_before_header_identical':True,'entire_postheader_suffix_identical':True,'postheader_sha256':hashlib.sha256(new[nb:]).hexdigest().upper()}
with (p/'comment-only-succession.json').open('x',encoding='utf-8') as f:json.dump({'frozen46_review_bytes_preserved':True,'live47_capture_preserved':True,'files':rows,'fresh_successor_native_gate_required':True,'new_mathematical_acceptance':False},f,indent=2)
print(json.dumps(rows,indent=2))
