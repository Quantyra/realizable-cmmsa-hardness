# Three-lens closeout: readRatTag_of_tree

Source: `93d35131ed5317209ab456651387d4d9a2558fc2`
Certification: local target-fresh after GCP reauth failure (`4ca1d89` / `453fdf4`)

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Local frozen-blob compile main+Checks twice; objects `825FD451…` / `F6DFD04A…`; axioms standard trio. GCP reauth failed. |
| Proof-adversarial | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-read-rat-tree-fp-proof-adversarial-review.md` |
| Complexity | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-read-rat-tree-fp-complexity-theory-review.md`. Real `ratTree` reconstruction. |
| Non-claims | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-read-rat-tree-fp-nonclaims-review.md`. Not decodeInput ∈ FP. |

Accepted: `readRatTag_of_tree`.
Not accepted: `decodeInputTag_mem_FP`, Theorem 1, Corollary 2.
