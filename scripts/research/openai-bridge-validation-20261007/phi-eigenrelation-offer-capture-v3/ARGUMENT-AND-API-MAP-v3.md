# Exact Phi eigenrelation: v3 author milestone

The companion source now contains bodies for the complete target theorem chain:

1. `pairing_mul_right_rect` derives `pairing Y (B*C) = pairing (Y*Cᵀ) B`
   directly from the pinned entrywise definition.
2. `unrestricted_B_character_mean` applies character orthogonality on the
   complete unrestricted B carrier.
3. `matrix_rows_kernel_iff`, `row_li_iff_kernel_subtype_li`, and
   `kernelRowsEquiv` establish the row/kernel correspondence in both
   directions. `kernelSurvivorFrameEquiv` adds the full-row-rank condition and
   supplies the explicit inverse maps.
4. `kernelSurvivor_card` counts independent frames in `ker Y.mulVecLin`,
   including the impossible-dimension branch. `fullRowFrame_card` and
   `importedSurvivor_card` bind that count to the exact `FullRowFrame` carrier
   used in Phi.
5. `kernel_fraction_eq_product` uses the pinned frame duality and product
   formula with parameters c=d-s, s=s, i=i. `phiAverage_character_eigen` then
   proves the normalized character eigenvalue, and
   `phiAverage_rankProjection_eigen` states arbitrary-real-F eigenrelation
   with no `RightInvariant` premise.

The original operator interface only has a meaningful normalized full-row
frame carrier under `s≤d`; every Phi theorem here keeps this explicit guard.
The `i>d` rank-projection branch is zero because the filtered frequency sum is
empty; no claim is made that the product eigenvalue vanishes when s=0.

This is an author-source milestone only. No local Lean or Lake execution was
performed. The complete module remains uncompiled; in particular, the finite
sum normalization/interchange tactic script, dependent equivalence elaboration,
and exact pinned API elaboration are not yet settled by compiler diagnostics.
Root must capture these exact successor bytes before further edits. GCP native
verification, profiles, preserved receipts, mathematical review and manuscript
acceptance remain open.
