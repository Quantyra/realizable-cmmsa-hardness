# Complex coordinate one-step A15

`BinaryMatrixComplexA15.actualGlobal_A15_complex_fixedLine` and
`actualGlobal_A15_complex_fixedHyperplane` prove the coordinate domain-line
and codomain-hyperplane one-step norm-square globalness bounds for every
dimension, order `k`, fixed base column or row `t`, complex-valued function,
and nonnegative `ε`. The quantified premise and conclusion range over every
actual affine restriction at every base. The loss is exactly
`4 * 2 ^ (4 * (k + 1)) * ε`; empty and zero-dimensional fibres are included.

The proof keeps real and imaginary energies coupled as `Complex.normSq`.
It proves Jensen for the complex translation mixture, transports normalized
fibre energy under translation and the fixed-base embedding, and applies the
two polynomial factors with the original coefficient estimate. The
hyperplane case follows by transposing raw affine equations and fibres.

The complex polynomial is the direct complex-linear extension of the
coordinate line translation average and its transpose. Connecting its
rank-`k` restricted level to the manuscript hybrid derivative via complex
(A14), and transporting the coordinate line/hyperplane result through
arbitrary quotient/subtype bases, remain open. Thus the full arbitrary
carrier (A15), peeled influence bound, MZ NO decoder, and numeric
NO-soundness gap are not closed. The numeric gap is unchanged.

Target build: `lake build PvNP.RealizableHardness.BinaryMatrixComplexA15`
passed (2219 jobs). `lake build
PvNP.RealizableHardness.BinaryMatrixComplexA15Checks` passed (2220 jobs).
Both target theorems report only `[propext, Classical.choice, Quot.sound]`.
