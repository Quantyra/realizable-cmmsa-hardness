# Typed line reduced-carrier affine bijection

For every one-dimensional `L ≤ V/A`, codomain subtype `B`, and fixed
base `T`, `reducedMatrixEquiv` identifies `Hom((V/A)/L,B)` with the
matrix space having exactly the first `q` adapted domain columns.
`lineAdapted_symm_cast_mkQ` verifies the quotient basis on each such
column. Therefore `dropLast_lineMatrix_comp_mkQ` identifies the matrix
of `N∘q_L` after dropping the last column with `reducedMatrixEquiv N`.

`reducedAffineEquiv B L hL T` proves that the actual map
`N ↦ dropLastMatrix(lineMatrixEquiv(T+N∘q_L))` is a bijection onto the
reduced matrices. The affine offset is the dropped matrix of the
specified `T`; no base is replaced by zero. This is the exact domain
change needed to turn the prior coordinate A15 witness into a typed
reduced-carrier witness.

Actual affine restriction fibre/order/normalized complex normSq
transport on `Hom((V/A)/L,B)` is the next theorem. Until it and the
translated-output globalness are proved, full typed A15 remains open
and the numeric NO-soundness gap is unchanged.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedChecks`
passed (2296 jobs). Axiom audits of the fixed-base equation and affine
bijection report only `[propext, Classical.choice, Quot.sound]`.
