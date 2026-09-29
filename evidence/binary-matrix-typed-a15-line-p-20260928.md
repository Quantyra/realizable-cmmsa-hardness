# Typed line polynomial P conjugacy

`typedLineP_coordinate` proves that the intrinsic complex line operator
`(I−2^(j+1)E)(I−2^jE)` on `Hom(V/A,B)` equals the existing coordinate
`complexLineP` under the line-adapted matrix equivalence, pointwise for
every `j`, complex function, and matrix. This uses the exact uniform
translation-average comparison, with no extra loss.

The same adapted equivalence also maps every fixed-base line
restriction to `rawLastColumn` at the column determined by that base.
The remaining force comparison is preservation of the actual globalness
quantifier under this adapted equivalence, plus rank projection and
hybrid selector/derivative conjugacy. Full typed A14/A15 and the
manuscript influence bound remain open; the numeric NO-soundness gap is
unchanged.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA15OneStepChecks`
passed (2294 jobs). The P theorem's axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.
