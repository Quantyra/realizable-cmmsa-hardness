# Three-lens closeout: packed readFormulaTag FP

Source: `41c6e1ca1d4fc3d264d319fdd20cb65170b1851c`
Certification: local target-fresh after GCP reauth failure (`0210ae9`)

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Local frozen-blob compile main+Checks twice; objects `C118C1F7…` / `12273BFE…`; axioms standard trio |
| Proof-adversarial | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-read-formula-fp-proof-adversarial-review.md` |
| Complexity | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-read-formula-fp-complexity-theory-review.md`. Real iterate of formula stack machine; parent `formula_encode_le` width. |
| Non-claims | GO-WITH-NOTES | `research/reviews/2026-09-16-actual-read-formula-fp-nonclaims-review.md`. Not decodeInput ∈ FP. |

Accepted: `readFormulaTag ∈ Complexity.FP`.
Not accepted: `readFormulaTag_of_pair`, `decodeInputTag_mem_FP`, Theorem 1, Corollary 2.
