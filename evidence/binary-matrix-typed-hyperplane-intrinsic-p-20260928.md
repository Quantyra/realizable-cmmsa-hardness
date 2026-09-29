# Intrinsic hyperplane operator identification

The Lean module `BinaryMatrixTypedHyperplaneIntrinsicP` defines the finite uniform
translation average over every functional `φ : (V/A) → F₂` and every `w : B`
with `ψ(w)=1`, where `ψ` is the nonzero defining functional of the codimension
one hyperplane `H`. The theorem `hyperplaneDefiningFunctional_ker` proves
`ker ψ = H`. The finite index equivalence and rank one shift conjugacy show
that the normalization and every summand agree with the transpose coordinate
average. `intrinsicHyperplaneP_eq_typed` identifies the resulting polynomial
pointwise with `typedHyperplaneP`, for every complex function, matrix, and
rank parameter, including zero dimensional boundary cases.

This closes the **operator identity** needed for the typed hyperplane A15
one step. It does not prove the separate **selector identity**
`typedHyperplaneSelected B H hH Y ↔ ker Y ≤ H`; the existing typed A14
frequency bridge still expresses its selector in adapted coordinates. A typed
A1 peeling iteration, MZ decoder, outer contradiction, and final NO exponent
also remain open. This increment does not reduce the numeric NO soundness gap.

Verification: an independent local build of the Checks target passed 2,303
jobs. `#print axioms` for the kernel, average, and polynomial identity reported
only `propext`, `Classical.choice`, and `Quot.sound`. No GCP build or visible
console launch was used for this increment.
