# Typed codomain-hyperplane A15 one-step bound

`BinaryMatrixTypedA15HyperplaneReducedChecks` checks the actual typed
codomain-hyperplane one-step theorem. It quantifies over arbitrary quotient
`V/A`, subtype codomain `B`, codimension-one `H ≤ B`, fixed base
`T : V/A →ₗ B`, complex `f`, `k`, and nonnegative `ε`.

The theorem `typed_hyperplane_oneStep_A15_global` says actual normalized
complex norm-square globalness of `f` through order `k+1` implies actual
normalized globalness, through order `k`, of
`N ↦ typedHyperplaneP k f (T + H.subtype ∘ N)` on `Hom(V/A,H)`.
The factor is exactly `4 * 2^(4*(k+1)) * ε`.

The reduced carrier is quantified over every typed actual affine
restriction. The proof checks its fibre bijection, order, normalized energy,
and fixed-base translation into the complex coordinate theorem. The line
and hyperplane A15 one-step bounds are now both available on their typed
reduced carriers. The hyperplane A14 selector/rank identity and A1 peeling
into the iterated manuscript A15 influence bound remain open. This does
not improve the numeric MZ NO-soundness gap. The tagged arbitrary-fixed-table
representative-selection inequality with `2^-J` class-collision charge was
proved earlier. The original post-padding verifier-to-tagged source-law
handoff and MZ decoder remain open.
