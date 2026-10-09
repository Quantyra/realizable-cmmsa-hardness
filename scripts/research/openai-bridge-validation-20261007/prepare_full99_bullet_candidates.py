"""Preserve Full98 and derive only three Lean tactic-bullet repairs."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).parent
PINS = {
    'BinaryMatrixRightOrbit.lean': 'CBD5CCF80D2987D32A2F67D0B3E3314196DFB2F9EF73970C019DBE23ABC4554F',
    'BinaryMatrixRightFourierCovariance.lean': 'A8EE442EDBE223A733087496B87DA4A330A6FB278F56FEBDE4D7E5FCA439BA2D',
}

def sha(data):
    return hashlib.sha256(data).hexdigest().upper()

def main():
    parent = HERE / 'full98-matrix-fourier-candidates-v1'
    target = HERE / 'full99-matrix-fourier-bullet-repair-v1'
    target.mkdir()
    rows = []
    for name, pin in PINS.items():
        old = (parent / name).read_bytes()
        assert sha(old) == pin
        new = old
        if name == 'BinaryMatrixRightOrbit.lean':
            assert old.count(b'\n  - ') == 3
            new = old.replace(b'\n  - ', ('\n  ' + chr(0xb7) + ' ').encode('utf-8'))
            assert new.replace(('\n  ' + chr(0xb7) + ' ').encode('utf-8'), b'\n  - ') == old
        new.decode('utf-8', errors='strict')
        assert not new.startswith(b'\xef\xbb\xbf')
        (target / name).write_bytes(new)
        rows.append(dict(name=name, parent_sha256=pin, sha256=sha(new), bytes=len(new),
                         change='three ASCII hyphens replaced with Lean tactic bullets' if new != old else 'byte-identical'))
    receipt = dict(schema='full99-syntax-only-bullet-candidate-derivation-v1', sources=rows,
        exact_inverse_parity=True, statement_hypotheses_and_proof_route_preserved=True,
        failed_Full98_inputs_untouched=True, compiler_invoked=False, native_verified=False,
        universal_Spectral47_inhabitant_proven=False, accepted=False)
    (target / 'derivation.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
