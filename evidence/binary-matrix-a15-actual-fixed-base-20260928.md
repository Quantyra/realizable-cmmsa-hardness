# Fixed-base A15 under intrinsic actual affine globalness

Date: 2026-09-28 Pacific. S3132 finite binary matrix Appendix A13-A15.

The theorem `BinaryMatrixActualAffine.actualGlobal_A15_fixedBase` now states, for every finite `n,d,k`, every `ε≥0`, every real full-matrix function `f`, and **every fixed base column `t`**:

```
UpToActualSquareGlobal (k+1) ε f
  → UpToActualSquareGlobal k (4 * 2^(4*(k+1)) * ε)
      (rawLastColumnRestrict t (lineP k f)).
```

`lineP k` is the actual two-factor line-translation polynomial. This preserves the manuscript's `j=k+1` index, full up-to-order quantifier, arbitrary fixed base, and factor. The premise and conclusion quantify over intrinsic affine restrictions with domain-fixed subspace `A`, codomain variation subspace `B`, base `T`, order `dim A+codim B`, and fibre defined by `(M−T)|A=0` and `im(M−T)⊆B`.

The raw-to-actual bridge sends a consistent pair of equations `MU=V₀`, `XM=Y₀` to `A=range U`, `B=ker X`, and any solution `T`. It proves identical fibres and order at most the raw nominal budget. The reverse actual-to-raw bridge chooses bases of `A` and `W/B`, builds right and left matrices, and proves identical fibres with nominal budget **equal** to actual order. Both directions preserve the normalized uniform measure by exact finite-set equality, including zero-dimensional spaces. An inconsistent raw fibre contributes zero under `ε≥0`.

The intrinsic fibre predicate is mathematically the affine coset `T+Hom(V/A,B)`. A direct Lean factorization theorem through the quotient and inclusion has **not** yet been proved; the fixed-base A15 statement should be read against the explicit intrinsic carrier until that equivalence is checked. The coordinate A14 rank identity is in `BinaryMatrixLineA14.lean`. Iterating first derivatives to arbitrary `(A,B,T)` via A1, the final influence (A15), A22, positive-rank hypercontractivity, MZ decoder, and Theorem 1 remain open. This increment does not change the numeric NO-soundness gap.

Verification: local targeted `lake build PvNP.RealizableHardness.BinaryMatrixActualAffineChecks` and `#print axioms actualGlobal_A15_fixedBase`; only `[propext, Classical.choice, Quot.sound]` are expected. No GCP connection or visible console was launched.
