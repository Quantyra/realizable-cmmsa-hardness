# Source-star completeness complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `c574bd9549543368f26902447a33c7c3427fef3e`. Independently rehashed main `192ABD6EA975620C5161FDEEB655F346488911A04CEB24970DBEBE8AE534E648`, Checks `2C8E0B3D1D80C024B7F68C6F6D5850F3E683D96970818460F89EAD638274097D`; objects `0E22937A…68D3` / `CA88A2BA…06F9`. Evidence `research/evidence/2026-09-16-actual-source-star-completeness-fresh-run/` gate PASS naming `c574bd9`. `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean.

## Force

`honestRawLabel` is the ambient pairing `z ↦ ∑_i z_i x_i`. `honestRawLabel_eval_equation` is force-bearing: pairing with `equationVector` (indicator of a 3-set) equals the three-variable sum, via `support_eq`, `row_injective`, and `Fin.sum_univ_three`. `honestRawLabel_respects_iff` is the YES leaf correspondence: `RespectsAt` of that pairing on a presented leaf iff every queried row has `badRow x e = false`. Quantifiers are honest: presented `P.U`, not the whole instance.

`restrictionAgreesOnCenter_honest` is the related-pair YES transport. It is not identity `Rel` of identical labels: `P.Rel Q` may be distinct presentations (Checks use original rows 0 and 1, different `U`, domains related by `domain ⊔ H`). Both `restrictToCenter` maps equal the same pairing with `x`, then `restrictionAgreesOnCenter_iff_source` converts to transported agreement on hypothesized shared `K`. `k` is a parameter; the theorem is not silently `K=⊥`. `RespectsAt` is used to package `LeafLabel`s, not in the `K`-algebra; that is the right completeness shape (YES ⇒ packable honest labels that then agree).

## Theater

`starAccepts_honest` is identity `Rel` of identical labels: `vs = ws`, `hrel = Rel.refl`, same centers, same `honestPackaged` family on both sides. For each `i` the star test compares a leaf to itself. On `Rel.refl` and equal labels, `restrictionAgreesOnCenter_iff_source` reduces to `restrictToCenter ∘ id = restrictToCenter`, which holds for any packaged label, not because the labels are honest YES pairings. The cross-index hypothesis `∀ i j, (Cs i).K = (Cs j).K` is unused in the proof. Do not call this completeness of a two-sided star (`vs i` related to a possibly distinct `ws i`). The pair-level theorem already supplies the related-pair content; `starAccepts_honest` does not lift it.

## Checks and non-credits

Checks invoke shipped theorems on a nonempty three-row mixed-RHS fixture (assignment matches the unique nonzero-RHS original support bit) and on empty `J=h=0` with the zero assignment; `n=1` and `n=2`; `#print axioms` standard. Centers are `k=0`, `K=⊥` (freeze-permitted). Related-pair agreement is therefore not witnessed on a nontrivial center. `n=2` still uses `Rel.refl` per index, even though `twoPresented 0` and `twoPresented 1` are distinct.

Not NP-hardness. Not NO/soundness, decoding, `leafFailIndicator` bounds, `SeededMap`, or a probability law. No `PMF`, no expectation, no measure, no switching-quality ratio. Not credited: Theorem 1, Corollary 2, randomized reduction, P vs NP.

Usable as leaf YES-completeness and related-pair honest agreement on shared `K`. Next consumer remains NO/soundness: bound `leafFailIndicator` of non-honest labels by source-extension failure. Do not skip to Theorem 1.
