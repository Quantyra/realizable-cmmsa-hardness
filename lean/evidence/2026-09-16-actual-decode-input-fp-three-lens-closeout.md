# Three-lens closeout: decodeInputTag_mem_FP

Source: `f7f338bdd28101ff66fa482716a435ca783cd191`
Certification: `29a8713` (local after GCP reauth failure)

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Local frozen-blob compile main+Checks twice; objects `773E1476…` / `BB977DD6…`; axioms standard trio |
| Proof-adversarial | GO-WITH-NOTES | `lean/reviews/2026-09-16-actual-decode-input-fp-proof-adversarial-review.md` |
| Complexity | GO-WITH-NOTES | `lean/reviews/2026-09-16-actual-decode-input-fp-complexity-theory-review.md`. Real packed `readInput` compose then `decodeInputTag ∈ FP`. |
| Non-claims | GO-WITH-NOTES | `lean/reviews/2026-09-16-actual-decode-input-fp-nonclaims-review.md`. Not `selectedPairedRun_mem_FP`. Not Theorem 1. |

Accepted: `readInputTag_mem_FP`, `readInputTag_of_tree`, `decodeInputTag_mem_FP`.
Not accepted: `selectedPairedRun_mem_FP`, `selectedSeededMap`, inhabited `hSrcCmmsa`, Theorem 1, Corollary 2.
