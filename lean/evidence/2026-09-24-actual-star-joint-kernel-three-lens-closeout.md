# Three-lens closeout: bounded S3132 ActualStarJointKernel

Date: 2026-09-24

Source base: `d6e59e2eca47031a31b0795587b4df2cea9540ba`

Main SHA-256: `f02b9c19a7145c07eefa78693e24ca4eade747303e75300ebdc54563bd12d40f`

Checks SHA-256: `38cd8e0488cae0bb8c5892fce6dba6cb26a6f14bfca8b70c913be595ed42f761`

GCP evidence: `artifacts/gcp_actual_star_joint_kernel_r8_20260924T170258Z`

## Verification

R8 result: **PASS**. Dependency, direct main, direct checks, combined, and both replay builds returned zero. The direct/replay logs and `.olean` hashes were stable, the source gate and forbidden-shortcut scan passed, and the two printed theorem reports used only `propext`, `Classical.choice`, and `Quot.sound`. The evidence manifest and complete-history bundle verified, and the VM's independently checked final status was `TERMINATED`.

The source hashes in the R8 checkout metadata and local verification receipt match the frozen files above. R8's replay diff is clean. The proof review's driver replay-diff status-robustness observation is retained as a future harness note, not a defect in this run or these Lean files.

## Three-lens table

| Lens | Verdict | Review / bounded note |
|------|---------|-----------------------|
| Proof-adversarial | GO-WITH-NOTES | [`2026-09-24-actual-star-joint-kernel-proof-adversarial-review.md`](../reviews/2026-09-24-actual-star-joint-kernel-proof-adversarial-review.md). R8 is clean; harden future driver replay-diff status handling. |
| Complexity theory | GO-WITH-NOTES | [`2026-09-24-actual-star-joint-kernel-complexity-theory-review.md`](../reviews/2026-09-24-actual-star-joint-kernel-complexity-theory-review.md). Accepts only the bounded algebraic kernel characterization. |
| Non-claims boundary | GO-WITH-NOTES | [`2026-09-24-actual-star-joint-kernel-nonclaims-review.md`](../reviews/2026-09-24-actual-star-joint-kernel-nonclaims-review.md). S3132 only; D3b2 was accepted separately and is not reopened here. |

## Accepted boundary

Accepted: bounded S3132 `ActualStarJointKernel`, identifying actual-star joint directness with injectivity of the full quotient-increment direct-sum map and identifying failure with a nonzero kernel witness.

Not established or credited: D3b2, any new source-star law, a quantitative kernel bound, a reduction soundness/completeness theorem, an FP result, unconditional Theorem 1, Corollary 2, or P-vs-NP. This closeout is not route-final.
