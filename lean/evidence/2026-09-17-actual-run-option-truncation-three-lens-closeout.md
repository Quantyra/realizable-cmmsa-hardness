# Three-lens closeout: runOptionGuardTag and runOptionTruncationTag

Date: 2026-09-17  
Source base: `c6dfbb4`  
Main SHA-256: `D05E20F6848FF374BB84DFCDD81553FDFFCB46CEE1A08B894A1C641B694845AE`  
Checks SHA-256: `44B6A155899B69C958D132772CF14FB7F31C1DC8A9E83B5388D8369248F5A8A0`  
README SHA-256: `329348FBAD30C52FA1AB940758780CBE244572440689DFB6D1E33409DB2905E0`  
PROVENANCE SHA-256: `C0DD27B24D04AF81E4BCABD2461690C22626AF653606168108BC64D9EB74A4C9`

## Verification

The fresh cloud-targeted build passed **2461/2461**; see [`target-build.log`](2026-09-17-actual-run-option-truncation-fresh-run/target-build.log). The fresh full Lake build passed **3961/3961**; see [`full-build.log`](2026-09-17-actual-run-option-truncation-fresh-run/full-build.log). The exposed declarations print only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, or new project axiom is credited.

## Three-lens table

| Lens | Verdict | Review / bounded note |
|------|---------|-----------------------|
| Proof-adversarial | GO-WITH-NOTES | [`2026-09-17-actual-run-option-truncation-proof-adversarial-review.md`](../reviews/2026-09-17-actual-run-option-truncation-proof-adversarial-review.md). Successful-decode semantic equality is soundly bounded; malformed guard fail-closed behavior is separate, and no malformed truncation theorem is claimed. |
| Complexity theory | GO-WITH-NOTES | [`2026-09-17-actual-run-option-truncation-complexity-theory-review.md`](../reviews/2026-09-17-actual-run-option-truncation-complexity-theory-review.md). Genuine bounded `takeLen` FP construction; valid-length corollary, full policy-output composition, checked executor, and selected-map FP remain. |
| Non-claims boundary | GO-WITH-NOTES | [`2026-09-17-actual-run-option-truncation-nonclaims-review.md`](../reviews/2026-09-17-actual-run-option-truncation-nonclaims-review.md). Documentation issue is resolved in this snapshot; `selectedSeededMap`, `hSrcCmmsa`, Theorem 1, Corollary 2, and P-vs-NP remain unclaimed. |

## Accepted boundary

Accepted: the cloud-verified packed `runOptionGuardTag_mem_FP` / `runOptionGuardTag_eq` guard increment together with the packed `runOptionTruncationTag_mem_FP` / `runOptionTruncationTag_eq` bounded truncation increment. The semantic equalities require successful decoding. Malformed guard input is covered by the existing fail-closed guard theorem; there is no separate malformed truncation theorem.

Not established or credited: a complete valid-length/product corollary, full policy-output composition, `checkedBits`, `accepted`, output-tree construction, `selectedPairedRun_mem_FP`, `selectedSeededMap`, inhabited `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, or P-vs-NP. This is not route-final.

The closeout records evidence for this exact snapshot only; it does not certify the manuscript's remaining end-to-end theorem.

