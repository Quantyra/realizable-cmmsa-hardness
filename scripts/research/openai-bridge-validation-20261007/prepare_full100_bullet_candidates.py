"""Repair only the remaining Fourier tactic bullets, preserving Full99 bytes."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).parent
PINS = {'BinaryMatrixRightOrbit.lean':'409FD652E1F051E92688466EAC57BD6B85AF93866D5F5D4C9AA0152AB25286B0',
        'BinaryMatrixRightFourierCovariance.lean':'A8EE442EDBE223A733087496B87DA4A330A6FB278F56FEBDE4D7E5FCA439BA2D'}

def sha(data): return hashlib.sha256(data).hexdigest().upper()

def validate(data):
    text = data.decode('utf-8',errors='strict')
    assert not data.startswith(b'\xef\xbb\xbf')
    assert not re.search(r'(?m)^\s*-[ \t]+',text), 'ASCII tactic bullet remains'
    assert not re.search(r'\b(sorry|admit|axiom)\b',text)
    assert not re.search(r'\?(?!_)',text)
    assert text.count('\nend\nend ') == 1

def main():
    parent = HERE/'full99-matrix-fourier-bullet-repair-v1'
    target = HERE/'full100-matrix-fourier-bullet-repair-v1'; target.mkdir()
    rows=[]
    for name,pin in PINS.items():
        old=(parent/name).read_bytes(); assert sha(old)==pin
        count=2 if name=='BinaryMatrixRightFourierCovariance.lean' else 0
        assert old.count(b'\n  - ')==count
        replacement=('\n  '+chr(0xb7)+' ').encode('utf-8')
        new=old.replace(b'\n  - ',replacement)
        if count: assert new.replace(replacement,b'\n  - ')==old
        else: assert new==old
        validate(new); (target/name).write_bytes(new)
        rows.append(dict(name=name,parent_sha256=pin,sha256=sha(new),bytes=len(new),repaired_bullet_count=count))
    receipt=dict(schema='full100-two-Fourier-bullet-repair-v1',sources=rows,
        exact_inverse_parity=True,all_remaining_ASCII_tactic_bullets_rejected=True,
        statement_hypotheses_and_proof_route_preserved=True,failed_Full99_inputs_untouched=True,
        compiler_invoked=False,native_verified=False,universal_Spectral47_inhabitant_proven=False,accepted=False)
    (target/'derivation.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
