# ActualStarJointKernel complexity-theory review

**Verdict: GO-WITH-NOTES**

Reviewed source base: `d6e59e2eca47031a31b0795587b4df2cea9540ba`. Main SHA-256: `f02b9c19a7145c07eefa78693e24ca4eade747303e75300ebdc54563bd12d40f`. Checks SHA-256: `38cd8e0488cae0bb8c5892fce6dba6cb26a6f14bfca8b70c913be595ed42f761`.

R8 GCP evidence at `artifacts/gcp_actual_star_joint_kernel_r8_20260924T170258Z` records `RESULT=PASS` with six checked declarations/directives, stable direct/replay outputs, a passing source gate, and a passing axiom allowlist.

The accepted S3132 increment is algebraic: it relates the existing actual-star `jointlyDirect` predicate to injectivity of a finite direct-sum linear map and represents failure by a nonzero kernel element. It supplies no algorithm, runtime bound, reduction, or new complexity-class membership result.

This review does not credit D3b2, which was accepted earlier and independently. It also does not establish a quantitative kernel estimate, unconditional Theorem 1, Corollary 2, or P-vs-NP.
