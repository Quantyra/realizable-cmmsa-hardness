# Actual affine globalness controls the raw A15 premise

Date: 2026-09-28 Pacific. S3132 finite binary matrix Appendix A15.

`BinaryMatrixActualAffine.lean` defines an intrinsic actual affine restriction by a fixed domain subspace `A`, permitted codomain variation subspace `B`, and base matrix `T`. Its fibre consists of maps `M` for which `(M−T)|A=0` and `im(M−T)⊆B`; its order is `dim A+codim B`. This is the intrinsic description of the manuscript coset `T+Hom(V/A,B)`, but the quotient/inclusion factorization equivalence has not yet been proved in Lean and remains an explicit representation obligation.

For every **nonempty** raw affine fibre with right equations `MU=V₀` and left equations `XM=Y₀`, choose any solution `T`. Taking `A=range U` and `B=ker X` gives exactly the same finite fibre. The order is `rank U+rank X≤columns U+rows X`, including rectangular and zero-dimensional cases. Therefore manuscript up-to-`r` squared globalness on every actual affine restriction implies `UpToRawSquareGlobal r ε`, with inconsistent raw fibres contributing zero when `ε≥0`. The proof uses equality of finite fibres, so normalized conditional measure is identical. The manuscript premise already covers all actual orders **at most** `r`; exact-order padding is irrelevant here.

The composed theorem `actualGlobal_A15_fixedBase_rawOutput` applies the previous raw A15 estimate at the exact factor `4·2^(4(k+1))` and arbitrary fixed base `t`. Its conclusion still quantifies over **raw** reduced restrictions. A reverse representation (every actual reduced fibre as raw equations with nominal budget at most actual order) is required before claiming the full actual-output A15 witness. Iteration to (A15), positive-rank hypercontractivity, MZ decoder, and Theorem 1 remain open. The numeric NO-soundness gap is unchanged.

Verification: targeted local Checks build and standard-axiom print are recorded by `BinaryMatrixActualAffineChecks.lean`. No GCP connection or visible console was launched.
