# MZ v1 hyperedge analytic gap (2026-09-28)

Source: Minzer–Zheng, *Near Optimal Hardness of Approximating k-CSP*,
[arXiv:2510.23991v1](https://arxiv.org/pdf/2510.23991v1), §§4.1–4.2.
The manuscript's `paper/submission-manuscript.md` gives a finite binary
reconstruction in Appendix `thm:binary-hc`.

The current Lean `MatrixGrassmannIdentity.grassmann_le_twice_moment` supplies
the rank-conditioned Grassmann-to-matrix comparison underlying MZ Lemma 4.4.
It does not bound the matrix moment. The first missing analytic theorem in the
MZ Lemma 4.1 route is the finite binary specialization of Theorem 4.6
(EKL24): for **every** Boolean function on a finite binary matrix space
whose density is at most `δ` on **every nonempty consistent** affine
restriction `MU = V₀, XM = Y₀` of nominal budget `r`, every `i ≤ r`, and
every dyadic `p ≥ 4`,

```text
  ‖rankFourierProjection i F‖ₚ ≤ 2^(500 * i^2 * p) * δ^(1 - 2/p).
```

Here `0 ≤ δ ≤ 1`, the restriction budget counts prescribed columns plus
prescribed rows even when these are dependent, and all norms and densities
use uniform probability. An empty inconsistent fibre has no conditional
density. The rank-zero, zero-density, and zero-dimensional cases remain in
scope. A suitable Lean target must define the binary character pairing,
normalized Fourier coefficients, rank-level projection, actual affine
restrictions, conditional density, and normalized `Lp` norm. No existing
Lean declaration in this repository supplies this theorem or its Fourier
infrastructure.

The appendix proof requires the hybrid Fourier filter and derivative
composition (A1), influence energy and density estimates, and the
finite-matrix global hypercontractive inequalities (A18), (A21), (A22).
After this theorem, the source path still requires MZ Lemma 4.7's
cross-level spectral estimate and the Hölder/high-degree split of Lemma 4.8
to bound `MatrixGrassmannIdentity.matrixMoment`; only then does Lemma 4.1
feed Theorem 4.2. MZ24's earlier two-query result does not supply the
multi-leaf hyperedge estimate.

This audit adds no Lean theorem and does not reduce the quantitative
NO-soundness gap. It identifies the first missing source-derived analytic
contract; treating the manuscript appendix as a Lean proof would be invalid.
