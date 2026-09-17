# Three-lens closeout: packed Tree.parse FP tag

Source: `52b57f29cd7d317bfa77a6d046f58ce3d44633a7`
Certification: `6cdf45bfa10fe10144b5e5b0c603d5a6740c1165`
Reviews: `c14fb93` (proof-adversarial) plus complexity/non-claims review commit.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Isolated target-fresh 7-stage compile; main+Checks twice; objects `BEF82D9A…F34F` / `3E17CACA…3D21`; rehash PASS 61/0; axioms `propext`, `Classical.choice`, `Quot.sound`; forbidden scan clean |
| Proof-adversarial | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-tree-parse-fp-proof-adversarial-review.md`. Total packed parser; iterate agrees on every `z`; rest not dropped. Notes: Checks malformed coverage is `[]` and `[true]` only. |
| Complexity | GO | `research/reviews/2026-09-16-actual-tree-parse-fp-complexity-theory-review.md`. Real Cobham `iterate_mem_FP` of packed `Tree.parse`, ruler `3(|z|+1)`, width `16(|z|+1)`. Not NP-hardness. |
| Non-claims | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-tree-parse-fp-nonclaims-review.md`. Wording is `treeParseTag ∈ FP` only. Not `decodeInput ∈ FP`, not Theorem 1. |

Accepted: `treeParseTag ∈ Complexity.FP`, total on malformed inputs.
Not accepted: `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.
