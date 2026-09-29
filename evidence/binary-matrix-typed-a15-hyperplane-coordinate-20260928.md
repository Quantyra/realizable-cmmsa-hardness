# Typed codomain-hyperplane A15 coordinate comparison

The Lean target `BinaryMatrixTypedA15HyperplaneChecks` checks the exact
adapted-row comparison on the manuscript's quotient/subtype carrier. For an
arbitrary codimension-one submodule `H ≤ B` and arbitrary prescribed
`T : V/A →ₗ B`, `hyperplaneMatrix_rawLastRow` shows every map
`T + H.subtype ∘ N` has precisely `T`'s final adapted output row.

`hyperplane_coordinate_fibre_image`, `_energy`, and `_order` establish a
bijection of **actual affine** restrictions, equality of restriction order,
and equality of normalized complex norm-square energy. Consequently
`typed_global_iff_hyperplane_coordinate` preserves every fixed restriction
quantifier. Applying the complex coordinate A15 hyperplane theorem gives
`typed_hyperplane_coordinate_witness_global` at exactly
`4 * 2^(4*(k+1)) * ε`; the fixed-base witness identity uses the same `T`.

This is the coordinate-carrier witness. Transport to the reduced typed
carrier `Hom(V/A,H)` and the intrinsic A14 rank/selector identity remain open.
It does not yet discharge the manuscript's iterated A15 influence bound or
the tagged arbitrary-fixed-table representative-selection inequality.
The numeric MZ NO-soundness gap is unchanged.
