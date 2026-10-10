"""Independent bounded frame enumeration; no Lean or universal proof claim."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import re


def count_frames(n, k):
    count = 0
    for columns in product(range(2**n), repeat=k):
        span = {0}
        for column in columns:
            if column in span:
                break
            span |= {x ^ column for x in tuple(span)}
        else:
            count += 1
    return count


def main():
    counts = {(n, k): count_frames(n, k) for n in range(4) for k in range(4)}
    checked = []
    for d in range(4):
        for c in range(d+1):
            s = d-c
            for i in range(d+1):
                a = Fraction(counts[c, i], counts[d, i])
                b = Fraction(counts[d-i, s], counts[d, s])
                eigenvalue = Fraction(1)
                for j in range(s):
                    eigenvalue *= Fraction(2**(d-i)-2**j, 2**d-2**j)
                assert a == b == eigenvalue
                checked.append(dict(c=c, s=s, i=i, numerator=a.numerator, denominator=a.denominator))
    assert counts[2, 3] == 0  # i>d, s=0: total quotient 0 versus empty product 1.
    folder = Path(__file__).parent/'frame-product-duality-candidate-v1'
    files = []
    for path in sorted(folder.glob('*.lean')):
        data = path.read_bytes(); text = data.decode('utf-8')
        assert not data.startswith(b'\xef\xbb\xbf')
        assert not re.search(r'\b(?:sorry|admit|axiom)\b', text)
        assert not re.search(r'(?m)^\s*set_option linter\.', text)
        files.append(dict(path='lean/PvNP/RealizableHardness/'+path.name,
                          bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
    record = dict(schema='frame-product-duality-bounded-independent-counts-v1',
                  checked_cases=checked, actual_frame_counts=[dict(n=n,k=k,count=v) for (n,k),v in counts.items()],
                  rank_guard_negative_case=True, files=files, native_verified=False,
                  independent_material_review=False, universal_proof_accepted=False)
    with (folder/'candidate.json').open('x', encoding='utf-8') as file:
        json.dump(record, file, indent=2); file.write('\n')
    print(json.dumps(dict(bounded_cases=len(checked), files=len(files), native_verified=False)))


if __name__ == '__main__':
    main()
