# Typed A14 spectral transport on the line and reduced carriers

The line-adapted input frequency equivalence maps every intrinsic
frequency `Y : B → Hom(V/A,F₂)` to the coordinate frequency matrix.
It preserves trace characters and rank exactly. Finite uniform complex
Fourier coefficients, every rank projection, and the selected-line
hybrid filter are therefore conjugate to the corresponding coordinate
definitions. This retains frequency collisions in the full Fourier
sum; no injectivity assumption on a restricted frequency is used.

The reduced carrier `Hom((V/A)/L,B)` has an analogous intrinsic
frequency equivalence. Its trace, rank, Fourier coefficient, and full
rank projection agree exactly with the reduced coordinate matrix
definitions.

These two comparisons feed the fixed-base coordinate complex A14
theorem. The remaining exact theorem is translation covariance of
complex rank projection: the arbitrary base `T` contributes free
reduced columns `c`, so the reduced typed witness is the coordinate
witness evaluated at `X+c`. Once that phase is transported, coordinate
A14 yields the intrinsic typed derivative identity. Codomain
hyperplane and A1 peeling remain open. The numeric NO-soundness gap is
unchanged.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA14LineChecks
PvNP.RealizableHardness.BinaryMatrixTypedA14ReducedChecks` passed
(2300 jobs). Axiom audits for both rank-projection bridges and the
selected-line filter bridge report only
`[propext, Classical.choice, Quot.sound]`.
