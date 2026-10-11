# Exact Phi eigenrelation continuation, v2

## The source-shaped target

Keep the imported interface `ExactAppendOperatorContracts.FullRowFrame s d`
and `phiAverage (s := s)`. The arbitrary real function F is expanded in the
existing Fourier basis. The pointwise character multiplier is independent of
F and requires no right-invariance assumption:

`Phi(character Y)(M) = [frameProduct (d - rank Y) s / frameProduct d s] * character Y M`.

Right-invariance remains a separate premise for the G/Phi composition and
restricted-adjoint identities. The character survives precisely when all C
rows lie in ker(Y.mulVecLin); it is killed when some row leaves that kernel.

## Exact unrestricted B mean

The corrected v2 source proves the rectangular identity directly from the
pinned `pairing` definition, whose summand is `Y i j * M i j`. It rewrites
`a * ∑ b` by `Finset.mul_sum`, swaps the finite j/k sums, then rewrites
`(∑ a) * b` by `Finset.sum_mul`. This avoids relying on a cyclic trace rewrite
and matches the complete source template in
`BinaryMatrixRightFourierCovariance.pairing_mul_right`.

After this identity, the fixed-C B average is character orthogonality against
the zero frequency, with the zero-frequency character and mean reduced using
the actual `character_zero_left` and `uniformMean_const` declarations. The
source theorem is `unrestricted_B_character_mean`.

## Exact kernel-frame count

For fixed Y, form the survivor subtype of the actual imported row frames:

`{C : FullRowFrame s d // Y * C.1.transpose = 0}`.

The row map sends C to `j ↦ ⟨fun k => C.1 j k, proof_row_j_in_ker⟩`. Its inverse
forgets the kernel proof and writes the resulting vectors as matrix rows.
Matrix extensionality gives both inverse laws. Entrywise matrix multiplication
shows `Y*Cᵀ=0` iff each row maps to zero under `Y.mulVecLin`. The pinned
`matrix_surjective_iff_rows_independent` identifies the full-row condition
with independence of the ambient rows; the subtype's injective linear map
preserves and reflects independence. Therefore the survivor subtype is
equivalent to `Frame (LinearMap.ker Y.mulVecLin) s`.

Rank-nullity for `Y.mulVecLin` and `rank_eq_finrank_range` give kernel
dimension `d - Y.rank`. Apply `card_frame` when `s ≤ d-Y.rank`. If this fails,
`Frame.fintype_card_le_finrank` makes the subtype empty and `frameProduct`
vanishes at the factor indexed by `d-Y.rank`. This gives exact survivor count
`frameProduct (d-Y.rank) s`, also at s=0. The full row-frame denominator equals
`frameProduct d s` by `card_surjective_coordinate_maps d s` and is positive
because s≤d.

## Identify the exact manuscript product

Assume i≤d and set c=d-s, so c+s=d. Apply the existing
`frameProduct_ratio_duality` with base c, appended width s and rank i. It
identifies

`frameProduct (d-i) s / frameProduct d s`

with `frameProduct (d-s) i / frameProduct d i`. Then
`frameProduct_ratio_eq_product` with the same parameters identifies this with
the exact s-factor product. This is the correct route from the kernel-frame
count; the earlier v1 note's direct invocation did not match the parameter
orientation of that API.

If i>d, the rank-i projection is the empty sum, hence identically zero. The
eigenrelation follows on both sides without asserting that the s-factor
product vanishes (it need not when s=0). This keeps the zero denominator branch
out of the argument. For i≤d, denominator `frameProduct d i` and the frame
carrier denominator `frameProduct d s` are positive, including zero-width
cases.

## Finish the arbitrary-F projection law

Expand `rankProjection i F` over its exact finite filtered frequency set.
Unfold the product carrier sum defining Phi and use finite sum interchange to
move that rank-frequency sum outside the independent B,C average. Apply the
pointwise character law to each frequency. Since every retained frequency has
rank i, the count above is constant across the whole filtered sum and factors
out. The remaining finite sum is exactly `rankProjection i F M`.

## Current status

`ExactPhiEigenrelation-v2.lean` is a successor source offer with a corrected
entrywise pairing proof and the exact unrestricted-B cancellation proof. The
kernel-frame equivalence/cardinality and final arbitrary-F projection theorem
are not yet source bodies. No compile or kernel certification is claimed.
