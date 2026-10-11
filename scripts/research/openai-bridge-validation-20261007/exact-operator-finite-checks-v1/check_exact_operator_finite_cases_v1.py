"""Exact finite falsification checks; never Lean or general theorem evidence.

The independent representation is row-major bit matrices over F_2.  Fractions
are rational throughout.  All matrix/orbit bases of each listed finite carrier
are exhausted, including zero dimensions.  No random sampling is used.
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib
import json
import time
import traceback

HERE = Path(__file__).resolve().parent
DEST = HERE / "exact-operator-finite-checks-v1"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


@lru_cache(None)
def matrices(n, d):
    return tuple(product(range(1 << d), repeat=n))


def span(vectors):
    values = {0}
    for v in vectors:
        values |= {u ^ v for u in tuple(values)}
    return tuple(sorted(values))


@lru_cache(None)
def rank(A):
    return len(span(A)).bit_length() - 1


@lru_cache(None)
def image(A, d):
    return span(sum(((row >> j) & 1) << i for i, row in enumerate(A))
                for j in range(d))


def mul(A, B):
    """A has len(B) columns.  Output width is inherited from B's row bits."""
    out = []
    for row in A:
        value = 0
        for j, b in enumerate(B):
            if (row >> j) & 1:
                value ^= b
        out.append(value)
    return tuple(out)


def add(A, B):
    return tuple(a ^ b for a, b in zip(A, B, strict=True))


def append(X, B, c):
    return tuple(x | (b << c) for x, b in zip(X, B, strict=True))


def char(Y, M):
    return 1 if sum((y & m).bit_count() for y, m in zip(Y, M, strict=True)) % 2 == 0 else -1


def inverse(U):
    d = len(U)
    preimages = {}
    for x in range(1 << d):
        ux = sum(((u & x).bit_count() % 2) << i for i, u in enumerate(U))
        preimages[ux] = x
    if len(preimages) != 1 << d:
        raise ValueError("not invertible")
    return tuple(sum(((preimages[1 << j] >> i) & 1) << j for j in range(d))
                 for i in range(d))


def eigenvalue(d, s, i):
    value = Fraction(1)
    for j in range(s):
        # Nat subtraction in the formal target also covers i > d.
        value *= Fraction((1 << max(d - i, 0)) - (1 << j),
                          (1 << d) - (1 << j))
    return value


def check(condition, label, **witness):
    if not condition:
        raise AssertionError(json.dumps(dict(label=label, **witness), default=str))


def check_case(n, c, s):
    d = c + s
    Ws, Xs, Bs = matrices(n, d), matrices(n, c), matrices(n, s)
    Rs = tuple(R for R in matrices(d, c) if rank(R) == c)
    Cs = tuple(C for C in matrices(s, d) if rank(C) == s)
    GL = tuple(U for U in matrices(d, d) if rank(U) == d)
    orbits = tuple(sorted({image(W, d) for W in Ws}))
    check(bool(Rs and Cs and GL), "nonempty-frame-carriers", n=n, c=c, s=s)
    first_counts, bottom_inverse_counts = Counter(), Counter()
    mask = (1 << c) - 1
    block_checks = 0
    for U in GL:
        V = inverse(U)
        I = tuple(1 << i for i in range(d))
        check(mul(U, V) == I == mul(V, U), "paired-inverse", U=U, V=V)
        R = tuple(row & mask for row in U)
        S = tuple(row >> c for row in U)
        C = V[c:]
        first_counts[R] += 1
        bottom_inverse_counts[C] += 1
        for M in Ws:
            MS, MR = mul(M, S), mul(M, R)
            for B in Bs:
                # Subtraction equals addition over F_2, including empty matrices.
                check(mul(append(MR, B, c), V) == add(M, mul(add(B, MS), C)),
                      "append-block-identity", M=M, B=B, U=U, V=V)
                block_checks += 1
    check(set(first_counts) == set(Rs) and len(set(first_counts.values())) == 1,
          "uniform-first-column-frame-marginal")
    check(set(bottom_inverse_counts) == set(Cs) and
          len(set(bottom_inverse_counts.values())) == 1,
          "uniform-bottom-inverse-row-frame-marginal")

    # Exact independent (B,C) law; repetitions are retained with multiplicity.
    increments = Counter(mul(B, C) for B in Bs for C in Cs)
    for M in Ws:
        gt = Counter(image(append(mul(M, R), B, c), d) for R in Rs for B in Bs)
        phi = Counter()
        for Z, count in increments.items():
            phi[image(add(M, Z), d)] += count
        check(all(gt[o] * len(Cs) == phi[o] * len(Rs) for o in orbits),
              "G-after-T-equals-Phi-on-all-orbit-indicators", M=M)

    # A complete bilinear basis: K ranges over invariant orbit indicators;
    # H ranges over every base-matrix indicator.  Compare integer measures.
    left = Counter((image(append(X, B, c), d), X) for X in Xs for B in Bs)
    right = Counter((image(W, d), mul(W, R)) for W in Ws for R in Rs)
    check(len(Xs) * len(Bs) == len(Ws), "append-carrier-cardinality")
    adjoint_cells = 0
    for o in orbits:
        for X in Xs:
            check(left[o, X] * len(Rs) == right[o, X],
                  "restricted-adjoint-on-complete-bilinear-basis", orbit=o, X=X)
            adjoint_cells += 1

    # Character eigenvalues on every frequency, without an invariance premise.
    chars = {Y: tuple(char(Y, W) for W in Ws) for Y in Ws}
    for Y in Ws:
        actual = Fraction(sum(count * char(Y, Z) for Z, count in increments.items()),
                          len(Bs) * len(Cs))
        expected = eigenvalue(d, s, rank(Y))
        check(actual == expected, "Phi-character-eigenvalue", Y=Y,
              actual=actual, expected=expected)

    # Real rank projections of a complete invariant basis.  The Gram identity
    # is checked for TWO independently chosen functions and all listed levels.
    # Bilinearity gives a finite complexification check, but is not a Lean proof.
    levels = tuple(range(d + 2))  # includes the empty rank-(d+1) projection
    by_rank = {i: tuple(Y for Y in Ws if rank(Y) == i) for i in levels}
    projections, appended = {}, {}
    Windex = {W: j for j, W in enumerate(Ws)}
    for o in orbits:
        coeffs = {Y: Fraction(sum(chars[Y][j] for j, W in enumerate(Ws)
                                   if image(W, d) == o), len(Ws)) for Y in Ws}
        for i in levels:
            vals = tuple(sum((coeffs[Y] * chars[Y][j] for Y in by_rank[i]), Fraction())
                         for j in range(len(Ws)))
            projections[o, i] = vals
            appended[o, i] = tuple(sum((vals[Windex[append(X, B, c)]] for B in Bs),
                                      Fraction()) / len(Bs) for X in Xs)
    gram_cells = 0
    for o, p, i, j in product(orbits, orbits, levels, levels):
        left_gram = sum((x * y for x, y in zip(appended[o, i], appended[p, j], strict=True)),
                        Fraction()) / len(Xs)
        right_gram = (eigenvalue(d, s, j) *
                      sum((x * y for x, y in zip(projections[o, i], projections[p, j], strict=True)),
                          Fraction()) / len(Ws))
        check(left_gram == right_gram, "two-function-rank-Gram", o=o, p=p,
              i=i, j=j, left=left_gram, right=right_gram)
        if i != j:
            check(left_gram == 0, "cross-level-orthogonality", o=o, p=p, i=i, j=j)
        gram_cells += 1
    return dict(n=n, c=c, s=s, d=d, matrices=len(Ws), base_matrices=len(Xs),
                append_matrices=len(Bs), column_frames=len(Rs), row_frames=len(Cs),
                general_linear=len(GL), image_orbits=len(orbits),
                first_frame_multiplicity=next(iter(first_counts.values())),
                bottom_inverse_frame_multiplicity=next(iter(bottom_inverse_counts.values())),
                append_block_checks=block_checks, G_Phi_matrix_checks=len(Ws),
                restricted_adjoint_basis_cells=adjoint_cells,
                arbitrary_character_eigen_checks=len(Ws), gram_basis_cells=gram_cells,
                levels=list(levels), eigenvalues={str(i): str(eigenvalue(d, s, i)) for i in levels},
                all_exact_checks_passed=True)


def main():
    DEST.mkdir(exist_ok=False)
    (DEST / ".gitattributes").write_text("* -text whitespace=cr-at-eol\n", encoding="utf-8")
    script = Path(__file__).resolve()
    source = script.read_bytes()
    (DEST / script.name).write_bytes(source)
    # Frozen authoritative source references establish the formal notation
    # being modeled; this experiment does not execute or verify these sources.
    refs = [HERE / "full107-trace-qualified-source-record-v1/review-sources/lean/PvNP/RealizableHardness" / p
            for p in ["ActualFiniteFrameProductDuality.lean", "BinaryMatrixFourier.lean",
                      "ActualFixedFunctionalAppendOperator.lean"]]
    manifest = dict(script=dict(path=script.name, sha256=digest(script)),
                    source_references=[dict(path=str(p.relative_to(HERE)), sha256=digest(p)) for p in refs],
                    representation="row-major binary bit matrices; exact integer counts and Fraction rationals",
                    lean_execution=False, cloud_execution=False, random_sampling=False,
                    general_theorem_verified=False, complex_formalization_verified=False)
    (DEST / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    start = time.monotonic()
    results = []
    cases = [(n, c, s) for n in range(3) for c in range(4) for s in range(4 - c)]
    cases += [(3, 0, 2), (3, 1, 1), (3, 2, 0)]
    try:
        for case in cases:
            result = check_case(*case)
            results.append(result)
            with (DEST / "progress.jsonl").open("a", encoding="utf-8", newline="\n") as stream:
                stream.write(json.dumps(result, sort_keys=True) + "\n")
            print(json.dumps(dict(case=case, passed=True,
                                  elapsed_seconds=round(time.monotonic() - start, 3))), flush=True)
        final = dict(status="PASS_FINITE_CASES_ONLY", cases=results,
                     case_count=len(results), elapsed_seconds=time.monotonic() - start,
                     general_theorem_verified=False, lean_execution=False,
                     boundary="Finite exhaustive falsification checks only; no theorem, native, trace, review or manuscript acceptance.",
                     remaining="GCP candidate compilation/profiles/custody/trace, independent body review, complex formalization and full manuscript obligations.")
        (DEST / "result.json").write_text(json.dumps(final, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(dict(status=final["status"], case_count=len(results))), flush=True)
    except BaseException:
        (DEST / "failure.txt").write_text(traceback.format_exc(), encoding="utf-8")
        raise


if __name__ == "__main__":
    main()
