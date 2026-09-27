# Accepted-good-mass three-lens

Date: 2026-09-26. The reviewed statement is
`selected_transverseStar_equalLeaf_accepted_rankGood`.
It is not route-final. Theorem 1 and Corollary 2 are not claimed.
Full CMMSA stays partial.

The measured event is equal extensions on `starLaw` of
`transverseComplement`. `jointlyDirect` is rank-good. The bad-star event
of that draw is the negation of `jointlyDirect`. The intersection of equal
extensions with rank-good is empty, so the inequality is witnessed by
`r` equal to the equal-extension mass, which is strictly below `S/2`.
`starAcceptsCenter` is not the event in the mass theorem.

Local `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
exited 0 (3272 jobs). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

GCP replay debt: `gcp-replay-equal-leaf-inequality-2026-09-26`.
Auth for `dfredriksen@quantyra.org` is present. No replay was started.
The lenses below do not clear this statement as the manuscript
`starAcceptsCenter` inequality, so it is not sealed as that claim.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Checks target exits 0. Axioms are `propext`, `Classical.choice`, `Quot.sound`. No `sorry`. |
| Proof-adversarial | NO-GO | The mass theorem quantifies equal extensions `z.2 0 = z.2 1`, not `starAcceptsCenter`. The intersection with `jointlyDirect` is empty, so the witness is `r = Pr[equal]` and the inequality is `0 ≥ 0`. `q : QuestionCenter` remains a parameter. The fixed-star conditional is not used. |
| Complexity | NO-GO | The joint-law count `1 / gaussian(2·blocks − leafT, leafK)` is unconditional and is not hardness. Reading it as accepted-good mass inflates an empty rank-good intersection. |
| Non-claims | GO-WITH-NOTES | The formal statement does not claim Theorem 1, Corollary 2, an `FP` producer, route-final, or full CMMSA. README.md and MANUSCRIPT.md are unchanged. Wording that called `jointlyDirect` the bad-star event, or said equal extensions contain every `starAcceptsCenter` outcome, was removed after this review. |
