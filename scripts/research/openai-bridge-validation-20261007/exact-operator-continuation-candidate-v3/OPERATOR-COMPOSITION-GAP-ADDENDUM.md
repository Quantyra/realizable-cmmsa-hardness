# Historical v3 gap map (superseded by the implementation addendum)

This document records the gap status before the source additions in
`OPERATOR-COMPOSITION-IMPLEMENTATION-ADDENDUM.md`. Read that implementation
addendum for the current candidate source map; both remain uncompiled and
unaccepted.

Status: uncompiled research candidate. The source-level finite marginals below are concrete additions to the earlier offer; none has native proof acceptance.

## Concrete GL source results

`RectangularGLRowCompletion.lean` now identifies `InversePair d := {(U,V) | UV=VU=1}` with Mathlib `Matrix.GeneralLinearGroup`, completes each surjective rectangular matrix by the Full107 `same_range_matrix_right_orbit` theorem, and proves equal-prefix fibres are explicitly equivalent by right multiplication by the paired transporter and its inverse. The first-row normalized mean is `row_prefix_uniform_mean`. Its transpose bridge and inverse-pair transpose give the exact first-c-column full-frame mean `gl_column_prefix_uniform_mean`.

`RectangularGLSelectedRows.lean` extends this same argument to any surjective selector P. `selectedRowsMap P hP` is the actual map `(U,V) ↦ P*U`; `selectedFiber_equiv_nonempty` constructs both transporter directions and both inverse laws; `selected_rows_uniform_mean` applies the finite equal-fibre averaging theorem. `bottomRowsMatrix c s` is the matrix of `LinearMap.funLeft` along `Fin.natAdd c`, and the source gives its surjectivity using `funLeft_surjective_of_injective`. Hence `bottom_rows_uniform_mean` is the normalized marginal for the literal s-by-(c+s) bottom row frame carrier, with no `Fin (c+s) ≃ Fin (s+c)` reindexing.

`inversePairSwap` is the explicit involution `(U,V) ↦ (V,U)`. Consequently `bottomInverseRowsMap` is the bottom s rows of V, where V is the stored two-sided inverse of U, and `bottom_inverse_rows_uniform_mean` transports the just-proved row law through inversion. These proofs have no positive-dimension branch; the empty selector/frame cases are carried by the same Fin-indexed maps. The exact denominator is the finite full-frame cardinal, which is positive for these dimensions because s≤c+s.

## Exact operator identity to consume these marginals

The Full107 actual append API is `ActualFixedFunctionalAppendOperator.appendAverage` over every `BinaryMatrix n s`, and `appendBinaryMatrixEquiv` preserves the order “base columns, then appended columns.” For d=c+s, let P be `canonicalPrefixMatrix c s` and Q be `bottomRowsMatrix c s`. The needed append-selector bridge is the matrix identity

`appendBinaryMatrix X B = X * P + B * Q`.

For a paired inverse U,V, put R=U*P.transpose (the first c columns of U), S=U*Q.transpose (the last s columns of U), A=P*V (the first c rows of V), and C=Q*V (the bottom s rows of V). From UV=I, the block identities give R*A + S*C = I. For arbitrary M and every unrestricted B,

`appendBinaryMatrix (M*R) B * V = M + (B-M*S)*C`.

The exact `RightInvariant F` premise applies to this full n-by-d matrix and the same paired U,V, with no rank assumption on M or B. Thus the fixed-U append mean equals the mean over B of `F(M+(B-M*S)*C)`. Translation `B ↦ B-M*S` is a bijection on the entire n-by-s matrix carrier, so this is the independent unrestricted-B conditional mean defining Phi at C. Averaging U and applying the first-column and inverse-bottom marginals yields the exact `gAverage (appendAverage F) M = phiAverage F M` target. No independence of R and C is needed: the conditional equality holds pointwise in U before either marginal is taken.

The above displayed append-selector and block-product identities are the next exact source lemmas to write against `appendBinaryMatrix` and matrix `mul_apply`; they are not asserted as already present in the Lean candidate. In particular, do not replace B by a full-rank matrix or assume M has any rank.

## Adjoint and attached eigenrelation

The restricted adjoint uses the product-carrier equivalence `appendBinaryMatrixEquiv` and invariance only in the first argument K:

`uniformMean (fun M => appendAverage K M * H M) = uniformMean (fun W => K W * gAverage H W)`.

This is proved by the bijection `(M,B) ↔ appendBinaryMatrix M B`, followed by averaging the first-column GL marginal after right action on W; no unrestricted G=T-adjoint claim is needed. Rank projections `rankProjection i F` stay invariant when F is invariant, via the already-mapped dual-action lemma. The character eigenrelation belongs to phi_author's parallel candidate and must remain arbitrary-real-F; invariance is not a hypothesis on `Phi(rankProjection i F)`.

## API map and open declarations

| Needed source lemma | Actual API / exact proof input | State |
|---|---|---|
| Complete rectangular row frame | `same_range_matrix_right_orbit`, `LinearMap.range_eq_top.mpr`, `funLeft_surjective_of_injective` | Candidate in `exists_square_completion` and `exists_selected_completion` |
| Uniform first columns of U | row completion + transpose, `column_prefix_uniform_mean`, `inversePairEquivGL` | Candidate in `gl_column_prefix_uniform_mean` |
| Uniform bottom rows of U⁻¹ | arbitrary selector P, paired-inverse swap | Candidate in `bottom_inverse_rows_uniform_mean` |
| Actual append as selector products | Full107 `appendBinaryMatrix` / `appendBinaryMatrixEquiv`, `Matrix.mul_apply`, coordinate selectors P,Q | Not yet encoded as Lean lemma |
| Pointwise block identity and invariant substitution | Matrix associativity, UV=I, exact `RightInvariant` contract | Mathematical derivation above; not yet encoded |
| G(TF)=Phi F for invariant F | both marginals plus conditional B translation | Exact target; not yet encoded |
| Restricted adjoint | actual append product bijection, K invariant, first-column marginal | Exact target; not yet encoded |
| Phi rank-projection eigenrelation | `phiAverage_character_eigen`, finite Fourier expansion | Parallel phi_author candidate; arbitrary F, with s≤d |

The v1 and v2 offer files remain unchanged. This v3 source and this map are uncompiled and unreviewed; all proof-level claims are candidate translations pending the sole root build and required review.

Remaining to-do list: encode the selector append identity and block product in Lean; assemble exact G/Phi and restricted-adjoint sums; integrate phi_author's arbitrary-F eigenrelation with s≤d; then root performs native validation, GCP, trace/review, and acceptance.
