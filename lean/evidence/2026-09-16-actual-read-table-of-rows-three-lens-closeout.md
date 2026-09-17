# Three-lens closeout: readTableTag_of_rows

Source: `a59171452a27edff5eaf99365fbcf64e402a307f`
Certification: `f5995f2153c535675f71c137eb0b176fa522f7d7` (local after GCP reauth failure)

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Local frozen-blob compile main+Checks twice; objects `05288D3D…` / `E615ED35…`; axioms standard trio |
| Proof-adversarial | GO-WITH-NOTES | `lean/reviews/2026-09-16-actual-read-table-of-rows-proof-adversarial-review.md` |
| Complexity | GO-WITH-NOTES | `lean/reviews/2026-09-16-actual-read-table-of-rows-complexity-theory-review.md`. Real ValidRows tree agreement. |
| Non-claims | GO-WITH-NOTES | `lean/reviews/2026-09-16-actual-read-table-of-rows-nonclaims-review.md`. Not decodeInput ∈ FP. |

Accepted: `readTableTag_of_rows`.
Not accepted: `decodeInputTag_mem_FP`, Theorem 1, Corollary 2.
