# Actual source-star completeness non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `c574bd9549543368f26902447a33c7c3427fef3e`. Gate logs name `c574bd9`, not `bba6dbb`. Main `ActualSourceStarCompleteness.lean` SHA-256 `192ABD6EA975620C5161FDEEB655F346488911A04CEB24970DBEBE8AE534E648`. Checks SHA-256 `2C8E0B3D1D80C024B7F68C6F6D5850F3E683D96970818460F89EAD638274097D`. Evidence `research/evidence/2026-09-16-actual-source-star-completeness-fresh-run/`. Independently rehashed local sources match the freeze and the gate.

Accepted, completeness only:

- `honestRawLabel_respects_iff`: the honest pairing respects presented RHS on `P.U` iff `badRow` is false on `U`.
- `restrictionAgreesOnCenter_honest`: related honest packaged labels of the same assignment agree on a hypothesized shared `K`.
- `starAccepts_honest`: a `Fin n` family of honest packaged labels of that assignment, compared to itself under `Rel.refl`, satisfies `starAccepts`.

Theorems live in namespace `ActualPresentedLeafGluing`. The only source doc comment is the pairing definition. Checks invoke the exact exported signatures on a three-row mixed-RHS fixture (`k = 0`, `K = ⊥`) at `n = 1` and `n = 2`, plus the empty `J = h = 0` zero assignment. `#print axioms` is `propext`, `Classical.choice`, `Quot.sound` only.

Notes, not blocking:

- Module/commit titles that say "source-star completeness" are catalog labels. They are not NP-hardness, Theorem 1, Corollary 2, a NO/soundness decoder, `SeededMap`, or `P` versus `NP`.
- `starAccepts_honest` is diagonal self-comparison (`vs = ws`, `Rel.refl`). Related-pair YES transport is `restrictionAgreesOnCenter_honest`, not a related-family star against a distinct transported tuple. The unused family-wide `hK` hypothesis does not enlarge the proved claim.
- Checks may use `k = 0`; the theorem is parameterized by `k` and is not silently weakened to `K = ⊥`.
- This is not a packaging-only alias of `starAccepts`: honest pairing is constructed and shown to respect RHS / agree on `K`. It is also not manuscript completeness of source-to-star hardness.

Forbidden claims absent. Manuscript theorem incomplete. Next: NO/soundness (bound `leafFailIndicator` of non-honest labels by source-extension failure), then reduction assembly. Do not skip to Theorem 1.
