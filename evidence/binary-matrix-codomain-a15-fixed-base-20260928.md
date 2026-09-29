# Fixed-base codomain-hyperplane A15 sibling

Target: manuscript Appendix A13–A15, the coordinate codomain-hyperplane branch when the remaining domain constraint is zero. Source: `lean/PvNP/RealizableHardness/BinaryMatrixCodomainA15.lean`.

The theorem `actualGlobal_A15_fixedCodomainHyperplane` quantifies over every `n,d,k`, every fixed row base `t : Fin d → ZMod 2`, every real function on `(n+1) × d` binary matrices, and every nonnegative `ε`. From up-to-`k+1` squared globalness over **all actual affine restrictions**, it proves up-to-`k` squared globalness of the fixed-base hyperplane restriction after the actual transposed line polynomial, with manuscript loss `4 * 2^(4*(k+1)) * ε`. No degree assumption is used.

`transposeRaw_fibre` and `upToRawSquareGlobal_transpose` prove the nominal raw affine order and normalized fibre norm transport under matrix transposition. The pre-existing actual/raw equivalence transfers both quantifiers. The codomain operator `hyperplaneP` is defined by transposing the existing actual finite-translation line operator `lineP`, so this is its codomain-hyperplane translation distribution in the coordinate model. `rawLastRow` fixes the last codomain row to the requested base, including zero-dimensional cases.

Verification: `lake build PvNP.RealizableHardness.BinaryMatrixCodomainA15Checks` completed successfully (2219 jobs). `#print axioms actualGlobal_A15_fixedCodomainHyperplane` reports exactly `[propext, Classical.choice, Quot.sound]`; the new source/checks contain no `sorry` or custom `axiom`.

Scope: This proves the codomain one-step A15 **globalness** loss. It does not yet state or prove the codomain A14 rank-projection/derivative identity, arbitrary-subspace A1 peeling, full iterated A15, A22, positive-rank hypercontractivity, or the MZ NO decoder. It does not reduce the numerical NO-soundness gap.
