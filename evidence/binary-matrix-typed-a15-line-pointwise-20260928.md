# Typed complex A15 line: fixed-base and pointwise shift comparison

For every binary vector domain quotient `V/A`, codomain subtype `B`,
one-dimensional line `L` in `V/A`, and fixed base `T`, the adapted
coordinate equivalence maps `L` to the final coordinate line.
`lineMatrix_rawLastColumn` proves that every actual typed restriction
`T + N ∘ q_L` maps exactly to `rawLastColumn` with final column fixed
by `T`. The statement retains arbitrary `N` and base `T`.

`lineMatrix_rankOne_shift` proves pointwise conjugacy of an intrinsic
rank-one update `M + φ.smulRight w` with `φ(v_L)=1` to the coordinate
`lineShift` used by complex A14/A15. The codomain coordinates use the
same basis as the carrier comparison. `adaptedFunctional_inverse` and
`inverseAdaptedFunctional_last` construct the coordinate functional
inverse and verify its prescribed final value.

The finite index bijection and normalized sum comparison for the
translation average remain open, as do P, rank projection, the full
typed one-step A14/A15 theorem, and peeling to the manuscript A15
influence bound. This result does not reduce the numeric NO-soundness
gap.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA15OneStepChecks`
passed (2294 jobs). Axiom audits for the fixed-base diagram, index
inverse, and pointwise shift law report only
`[propext, Classical.choice, Quot.sound]`.
