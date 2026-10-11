# Exact Phi character eigenrelation: proof continuation

## Exact target

Use the pinned interface in `ExactAppendOperatorContracts`: `FullRowFrame s d`
is the subtype of actual `s × d` matrices whose `Matrix.toLin'` is surjective,
and `phiAverage (s := s) F M` averages independently over all unrestricted
`B : BinaryMatrix n s` and all such C. For every real F, without
`RightInvariant F`, prove

`phiAverage (s := s) (rankProjection i F) M = lambda(d,s,i) * rankProjection i F M`,

where `lambda(d,s,i)` is the exact s-factor product in the manuscript. The
real character calculation is termwise, so invariance is not involved here;
it remains needed for the G/Phi identity and restricted adjoint in the other
author's module.

## Character calculation

For a fixed frequency Y and row frame C, the rectangular trace-pairing identity
is

`pairing Y (B*C) = pairing (Y*C.transpose) B`.

It follows either by the trace identity in the pinned
`ActualFiniteAppendSpectral47.pairing_eq_trace_transpose_mul`, followed by
cyclicity of matrix trace, or by the complete entrywise proof template in
`BinaryMatrixRightFourierCovariance.lean` (replace the square column index by
`Fin s`). Thus character orthogonality on the entire unrestricted B carrier
gives

`uniformMean_B (character Y (B*C)) = if Y*C.transpose = 0 then 1 else 0`.

The source proof is included as `unrestricted_B_character_mean` in
`ExactPhiEigenrelation.lean`. This is a pointwise exact identity and retains
the zero width cases.

## Kernel-frame count, both directions

Define the survivor subtype

`{C : FullRowFrame s d // Y * C.1.transpose = 0}`.

Map each C to its ordered rows, with row j bundled as an element of
`LinearMap.ker Y.mulVecLin`. Conversely, for an independent ordered
s-frame in that kernel, forget each subtype proof and assemble those vectors
as the rows of C. Matrix extensionality proves both inverse laws. The
condition `Y*Cᵀ=0` is equivalent column-by-column to each row belonging to
`ker Y.mulVecLin`. Independence of the row family is equivalent to
surjectivity of `C.mulVecLin` by the pinned
`matrix_surjective_iff_rows_independent`; the subtype coercion into the
ambient coordinate space preserves and reflects linear independence. These
are exact equivalences, including s=0.

The kernel dimension is d-Y.rank: use
`Y.mulVecLin.finrank_range_add_finrank_ker`, `rank_eq_finrank_range` for the
actual matrix map, and `finrank_fin_fun`. If s ≤ d-Y.rank, `card_frame` gives
the numerator `frameProduct (d-Y.rank) s`. If not, the frame subtype is empty
by `fintype_card_le_finrank`; the same product is zero by its factor at index
d-Y.rank. The denominator is `frameProduct d s`, by
`card_surjective_coordinate_maps d s` and the same row-independence theorem;
it is positive since s≤d. Hence the survivor fraction is exactly
`frameProduct (d-Y.rank) s / frameProduct d s`, not an oracle or a conditional
surjection law.

## Extend from characters to every rank projection

Expand `rankProjection i F` as the existing finite sum over frequencies with
rank i. Finite-sum interchange in the independent product carrier and the
character calculation above reduce the result to the survivor fraction for
each frequency Y. Its rank is i, so the scalar is constant on this filtered
sum. The coefficient is `frameProduct (d-i) s / frameProduct d s`.

For i≤d, `frameProduct_ratio_eq_product` in the pinned
`ActualFiniteFrameProductDuality` rewrites it to the manuscript's exact
s-factor product. For i>d, the filtered frequency sum is empty (rank is at
most d), so both sides are zero; the product formula has a zero factor as
well. This explicit branch avoids a zero denominator. This establishes the
all-real-F pointwise eigenrelation once the kernel-frame equivalence and the
finite sum normalization are translated.

## Current author artifact and boundary

`ExactPhiEigenrelation.lean` contains the concrete rectangular trace identity
and unrestricted-B cancellation proof. It deliberately does not label the
kernel-frame equivalence or final eigenrelation as proved: those source bodies
remain to author and the current source has not been GCP compiled. In
particular, source-level availability is not native verification. The
operator, frame-completion, and restricted-adjoint laws remain owned by the
disjoint operator author.
