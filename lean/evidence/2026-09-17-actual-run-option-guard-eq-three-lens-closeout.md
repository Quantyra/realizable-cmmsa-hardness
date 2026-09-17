# Three-lens closeout: runOptionGuardTag_eq (historical earlier snapshot)

Date: 2026-09-17  
Source base: `c6dfbb4`  
Main SHA-256: `2500a41289666dfbe384642c17f61104a5013834e3a564b878af2d1591dd1e57`  
Checks SHA-256: `7432999fac70c80ae77fbfc6b832be3441b175c1781bef4a982b69dd1aa5441b`

This closeout records the earlier guard-only snapshot. It is historical evidence, not the current guard-plus-truncation closeout. The README issue noted below was subsequently resolved in the exact current snapshot; the historical hashes and table are preserved.

## Verification

Cloud-targeted build: **PASS**, 2461/2461. Full Lake build: **PASS**, 3961/3961. Exposed guard theorems use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, or new axioms.

## Three-lens table

| Lens | Verdict | Review / bounded note |
|------|---------|-----------------------|
| Proof-adversarial | GO-WITH-NOTES | [`2026-09-17-actual-run-option-guard-eq-proof-adversarial-review.md`](../reviews/2026-09-17-actual-run-option-guard-eq-proof-adversarial-review.md). No proof defect found; no concrete nonempty success example in Checks. |
| Complexity theory | GO-WITH-NOTES | [`2026-09-17-actual-run-option-guard-eq-complexity-theory-review.md`](../reviews/2026-09-17-actual-run-option-guard-eq-complexity-theory-review.md). Genuine packed length-guard FP/semantics only; next interface is outer policy/truncation, then checked executor. |
| Non-claims boundary | GO-WITH-NOTES | [`2026-09-17-actual-run-option-guard-eq-nonclaims-review.md`](../reviews/2026-09-17-actual-run-option-guard-eq-nonclaims-review.md). Boundary language was correct for the historical snapshot; its README issue was subsequently resolved. |

## Accepted boundary

Accepted: the bounded `runOptionGuardTag_eq` packed guard agreement, with the cloud-green and full-build evidence above.

Not established or credited: `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, or P-vs-NP. This is not route-final.

The documentation correction in `lean/README.md` was required for the historical snapshot and is resolved in the current guard-plus-truncation snapshot. This closeout records historical review evidence only; it does not edit Lean source or `lean/README.md`.
