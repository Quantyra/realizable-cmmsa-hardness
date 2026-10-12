"""Independent exact finite models, not Lean/kernel verification."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

S = Path(__file__).resolve().parent
source = S / 'numeric-visible-list-strategy-offer-20261011-v1/ActualVisibleListStrategy.lean'
expected = '1E7176008530D5D0BB0DEE16C428A295FFD08E6CB7BFEC34F0BAFEE46DC85D77'
assert hashlib.sha256(source.read_bytes()).hexdigest().upper() == expected
out = S / 'numeric-visible-list-strategy-finite-check-v1.json'
assert not out.exists()

def spaces(n):
    result = []
    for bits in range(1, 1 << (1 << n), 2):
        w = tuple(x for x in range(1 << n) if bits & (1 << x))
        if all(x ^ y in w for x in w for y in w):
            result.append(w)
    return result

def dim(w):
    assert len(w) & (len(w) - 1) == 0
    return len(w).bit_length() - 1

def dot(x, mask):
    return (x & mask).bit_count() % 2

def labels(n, w):
    return sorted({tuple(dot(x, mask) for x in w) for mask in range(1 << n)})

def restriction(pair, w):
    space, g = pair
    assert set(w) <= set(space)
    return tuple(g[space.index(x)] for x in w)

def extends(p, q):
    return set(p[0]) <= set(q[0]) and restriction(q, p[0]) == p[1]

vspaces = spaces(2)
espaces = spaces(3)
assert len(vspaces) == 5 and len(espaces) == 16
leaves = [w for w in vspaces if dim(w) == 1]
pairs = [(w, g) for w in vspaces for g in labels(2, w)]
visible = tuple(range(4))
assert len(pairs) == 11
counts = dict(table_parameter_cases=0, normalized_empty_list_branches=0,
              nontrivial_later_level_cases=0, compatible_member_bounds=0,
              original_extension_matching_bounds=0, exact_single_output_costs=0)

for bits in product(range(2), repeat=len(leaves)):
    table = {w: (0, b) for w, b in zip(leaves, bits)}
    def agreement(p):
        ls = [w for w in leaves if set(w) <= set(p[0])]
        return F(sum(restriction(p, w) == table[w] for w in ls), len(ls)) if ls else F(0)
    for r, c in product(range(3), [F(1, 2), F(1), F(4), F(20)]):
        counts['table_parameter_cases'] += 1
        lists = []
        law = {f: F(0) for f in range(4)}
        for j in range(r + 1):
            b = c / (4 * 5 ** j)
            ps = [p for p in pairs if 2 - dim(p[0]) <= r and agreement(p) >= b
                  and not any(p[0] != q[0] and extends(p, q) and agreement(q) >= b / 5
                              for q in pairs)]
            lists.append(ps)
            if not ps:
                counts['normalized_empty_list_branches'] += 1
                law[0] += F(1, r + 1)
                continue
            for p in ps:
                ext = [f for f in range(4) if tuple(dot(x, f) for x in p[0]) == p[1]]
                assert len(ext) == 2 ** (2 - dim(p[0]))
                for f in ext:
                    law[f] += F(1, (r + 1) * len(ps) * len(ext))
        assert sum(law.values()) == 1 and all(x >= 0 for x in law.values())
        for p0 in pairs:
            if 2 - dim(p0[0]) > r or agreement(p0) < c / 4:
                continue
            witnesses = [(j, p) for j, ps in enumerate(lists) for p in ps if extends(p0, p)]
            assert witnesses
            if not lists[0]:
                counts['nontrivial_later_level_cases'] += 1
            compatible = sum(mass for f, mass in law.items()
                             if tuple(dot(x, f) for x in p0[0]) == p0[1])
            for j, p in witnesses:
                assert compatible >= F(1, (r + 1) * len(lists[j]))
                counts['compatible_member_bounds'] += 1
        for w in espaces:
            if {x ^ y for x in w for y in visible} != set(range(8)) or 3 - dim(w) > r:
                continue
            intersection = tuple(x for x in w if x in visible)
            assert 2 - dim(intersection) == 3 - dim(w)
            for g in labels(3, w):
                p0 = (intersection, restriction((w, g), intersection))
                first_ext = [f for f in range(8) if tuple(dot(x, f) for x in w) == g]
                assert len(first_ext) == 2 ** (3 - dim(w))
                for f in range(4):
                    if tuple(dot(x, f) for x in intersection) == p0[1]:
                        exact_mass = F(sum((first & 3) == f for first in first_ext), len(first_ext))
                        assert exact_mass == F(1, 2 ** (3 - dim(w)))
                        counts['exact_single_output_costs'] += 1
                if agreement(p0) < c / 4:
                    continue
                joint = sum(mass * F(sum((first & 3) == f for first in first_ext), len(first_ext))
                            for f, mass in law.items())
                witnesses = [(j, p) for j, ps in enumerate(lists) for p in ps if extends(p0, p)]
                assert witnesses
                for j, p in witnesses:
                    assert joint >= F(1, (r + 1) * len(lists[j]) * 2 ** r)
                    counts['original_extension_matching_bounds'] += 1

assert counts['normalized_empty_list_branches'] > 0
assert counts['nontrivial_later_level_cases'] > 0
result = dict(schema='numeric-visible-list-strategy-finite-check-v1', passed=True,
              source_sha256=expected, arithmetic='exact fractions over binary dimensions2 and3',
              kernel_verification=False, source_accepted=False, **counts)
out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(result))
