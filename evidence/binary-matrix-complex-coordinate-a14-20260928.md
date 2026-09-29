# Complex coordinate A14

`BinaryMatrixComplexA14.complex_A14_fixedLine` and
`complex_A14_fixedHyperplane` prove the complex-valued coordinate (A14)
rank/derivative identities for every dimension, rank index, base column or
row, function, and output matrix. The complex rank projection and hybrid
derivative use direct normalized complex Fourier coefficients. Their real
and imaginary parts agree with the established real coordinate (A14),
whose full output projection aggregates coincident induced frequencies.
The polynomial is the complex `P` from the exact one-step norm-square
globalness proof at `b2753d2`. This covers `j=0` and zero dimensions.

This closes the coordinate complex (A14)/(A15) pairing. Transporting line
and hyperplane operators plus actual affine fibres through an arbitrary
quotient/subtype basis remains open; so the peeled full (A15) influence
bound and the numeric NO-soundness gap remain open. The numeric gap is
unchanged by this coordinate identity.

`lake build PvNP.RealizableHardness.BinaryMatrixComplexA14Checks` passed
(2292 jobs). Both theorem axiom audits report only `[propext,
Classical.choice, Quot.sound]`.
