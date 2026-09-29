# Adapted typed line A15 globalness and coordinate witness

For every quotient carrier `Hom(V/A,B)`, one-dimensional line
`L ≤ V/A`, complex function, actual affine restriction, and fixed base,
the line-adapted matrix equivalence preserves the actual restriction
fibre, its order, and normalized complex norm-square energy exactly.
`typed_global_iff_line_coordinate` quantifies over **all** actual
restrictions at every base in both directions, including the zero-order
and degenerate cases.

Using this equivalence, intrinsic P conjugacy, and the coordinate
complex A15 theorem, `typed_line_coordinate_witness_global` bounds the
reduced coordinate witness by precisely
`4 · 2^(4(k+1)) · ε` whenever the typed input is up-to-`k+1`
`ε`-global. `typed_line_coordinate_witness_fixed_base` proves that at
each typed input `N` the witness equals `P_k f(T+N∘q_L)` at the
specified base `T`; no zero-base substitution is made.

The conclusion's globalness is stated on reduced coordinate matrices.
The next exact theorem must identify those matrices and their actual
affine restrictions with `Hom((V/A)/L,B)` (then with the nested A1
carrier), preserving the affine base and normalized measure. Rank
projection and derivative A14 transport also remain open. Thus the
numeric NO-soundness gap remains unchanged.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA15AdaptedGlobalChecks`
passed (2295 jobs). Axiom audits of the full globalness equivalence
and both witness statements report only
`[propext, Classical.choice, Quot.sound]`.
