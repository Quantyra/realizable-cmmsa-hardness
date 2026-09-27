# Accepted-good-mass three-lens

Date: 2026-09-26. The statement is
`selected_transverseStar_starAcceptsCenter_rankGood` at
`b647f47feec70d8b1c8f11e040c842ba86022b70`.
It is not route-final. Theorem 1 and Corollary 2 are not claimed.
Full CMMSA stays partial.

`transverseStarAcceptsCenter` calls `starAcceptsCenter` on the presented
forms of both extensions of one `starLaw` draw on `transverseComplement`.
Acceptance implies the extensions are equal. The intersection with
rank-good `jointlyDirect` is empty, so the witness `r` is the acceptance
mass. That mass is at most `1 / gaussian(finrank − t, d − t)`, and
`selected_extensionCount_gt_halfMargin` puts the count strictly above
`2^{E+1}`, so `r < S/2`. The fixed-star conditional
`2^{-4 (h − h / bOf nRows)}` is not this probability.

GCP replay on `quantyra-lean-builder-01` (`us-central1-a`,
`quantyra-lean-cert-20260915`, Lean `4.34.0-rc2`):
`lake build --old PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
exited 0 (3272 jobs). Receipt:
`evidence/gcp/satellite/gcp_actual_star_starAcceptsCenter_b647f47`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | GCP replay of the checks target exited 0 (3272 jobs) at `b647f47`. Axioms are `propext`, `Classical.choice`, `Quot.sound`. No `sorry`. |
| Proof-adversarial | GO-WITH-NOTES | The inequality holds on this `starLaw`. Both drawn extensions are passed to `starAcceptsCenter`, acceptance sits inside the equal-extension event, and that event is disjoint from `jointlyDirect`. `r` is the acceptance mass, which is strictly below `S/2`. On its support the relation is `Rel.refl` of one canonical label, so there is no positive accepted-good mass. |
| Complexity | GO-WITH-NOTES | One `starLaw` is `centerLaw` then two independent extensions. The proved subtraction has left side identically 0 and is not force, an FP map, Theorem 1, or Corollary 2. `r` is not `2^{-4 (h − h / bOf nRows)}`. |
| Non-claims | GO-WITH-NOTES | The stop note does not claim Theorem 1, Corollary 2, P versus NP, route-final, or full CMMSA. README.md and MANUSCRIPT.md are unchanged. The module docstring still describes the equal-extension mass event beside this theorem. |
