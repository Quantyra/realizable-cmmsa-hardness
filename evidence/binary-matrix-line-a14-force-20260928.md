# Exact coordinate domain-line (A14) force result

Story: `stories/S3132-realizable-hardness-outer-game-and-star-pcp.md`.
Manuscript source: `paper/body.tex`, Appendix A, (A13)–(A14).

The theorem
`BinaryMatrixLineA14.rankProjection_rawRestrict_lineP_eq_hybridDerivative`
proves, for every `n d j : ℕ`, every fixed base column `t`, every real
function `f` on binary `n × (d+1)` matrices, and every reduced matrix `M`:

```lean
rankProjection j (rawLastColumnRestrict t (lineP j f)) M =
  hybridLineDerivative t (rankProjection (j + 1) f) M
```

Here `lineP j` is the actual manuscript polynomial `P_(j+1)` formed from the
uniform rank-one translation average; `hybridLineDerivative` is the raw
restriction after the final-codomain-line, full-domain hybrid Fourier filter.
The theorem covers `j=0`, so the selected rank-zero boundary is handled
without a negative-rank convention. Manuscript use at input rank `k≥1`
corresponds to `k=j+1`.

The proof first uses the exact rank identity
`rank Y = rank(dropLastFrequency Y) + [hybridLineSelected Y]` to show that
only input ranks `j` and `j+1` can reach output rank `j`. On the character
basis, the polynomial kills the unselected rank-`j` branch and retains the
selected rank-`j+1` branch. The output `rankProjection` uses binary Fourier
orthogonality on the *reduced* matrix space. Finite Fourier inversion then
sums all original frequencies, so equal induced frequencies collide and
aggregate with their actual coefficients and base phases.

This is the coordinate final-line/full-domain instance of (A14). It is not
the arbitrary-subspace hybrid composition (A1), the general line after a
coordinate change, or the positive-rank hypercontractive estimate (A22).
It does not reduce the numeric MZ NO-soundness gap or provide a decoder.
