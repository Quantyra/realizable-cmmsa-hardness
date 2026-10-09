"""Exact bounded dual-count audit, explicitly not a universal Lean proof."""
from fractions import Fraction
import hashlib
import json
from math import prod
from pathlib import Path
import sys

ROOT = Path(__file__).with_name('append-spectral-dual-count-audit-v1')


def frames(dimension, length):
    return prod(max(0, 2**dimension - 2**j) for j in range(length))


def main(verify=False):
    cases = []
    for c in range(13):
        for s in range(13):
            d = c + s
            for i in range(d + 1):
                image = Fraction(frames(c, i), frames(d, i))
                kernel = Fraction(frames(d - i, s), frames(d, s))
                gain = Fraction(1, 2**(i*s))
                if image != kernel or not 0 <= image <= gain or (i > c and image != 0):
                    raise RuntimeError('Bounded dual-count identity/gain failed')
                cases.append(dict(c=c, s=s, d=d, i=i,
                    image_ratio=[image.numerator, image.denominator],
                    kernel_ratio=[kernel.numerator, kernel.denominator],
                    gain=[gain.numerator, gain.denominator]))
    raw = (json.dumps(cases, indent=2) + '\n').encode()
    receipt = dict(schema='bounded-dual-frame-count-spectral-gain-audit-v1',
        cases=len(cases), case_sha256=hashlib.sha256(raw).hexdigest().upper(),
        c_s_each=list(range(13)), i_scope='0 <= i <= c+s',
        exact_integer_frame_counts_and_fraction_arithmetic=True,
        two_count_ratios_equal_in_all_tested_cases=True,
        ratio_at_most_2_to_minus_i_s_in_all_tested_cases=True,
        above_base_rank_cases_zero=True, proof_of_universal_identity=False,
        proof_of_uniform_GL_frame_distribution=False,
        proof_of_append_Parseval_ratio=False, kernel_or_native_execution=False,
        accepted=False)
    if verify:
        if (ROOT / 'cases.json').read_bytes() != raw:
            raise RuntimeError('Bounded audit case bytes changed')
        if json.loads((ROOT / 'receipt.json').read_bytes()) != receipt:
            raise RuntimeError('Bounded audit receipt changed')
    else:
        ROOT.mkdir()
        (ROOT / 'cases.json').write_bytes(raw)
        (ROOT / 'receipt.json').write_bytes((json.dumps(receipt, indent=2) + '\n').encode())
    print(json.dumps(receipt))


if __name__ == '__main__':
    if sys.argv[1:] not in ([], ['--verify']):
        raise SystemExit('Use initial audit or --verify of existing evidence')
    main(sys.argv[1:] == ['--verify'])
