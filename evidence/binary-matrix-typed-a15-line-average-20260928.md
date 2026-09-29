# Typed line averaging and exact coordinate conjugacy

For every quotient carrier `Hom(V/A,B)` and every one-dimensional line
`L ≤ V/A`, `lineFunctionalIndex` is an explicit equivalence between the
manuscript's uniform functionals satisfying `φ(v_L)=1` and the free
coordinate functionals on `Fin q`. Its product with the codomain basis
is a bijection of the two finite shift-index sets.

`typedLineAverage_coordinate` proves equality of the normalized complex
averages at every input matrix and for every complex-valued function.
It uses the pointwise rank-one update conjugacy and equal cardinalities,
so no distributional or numeric factor is lost. The exact fixed-base
restriction diagram from the prior commit is retained.

Conjugacy of the polynomial P and the rank projection, then the actual
typed A14/A15 one-step witness and peeling, remain open. This theorem
does not yet reduce the numeric NO-soundness gap.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA15OneStepChecks`
passed (2294 jobs). The average theorem's axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.
