# Accepted-good-mass three-lens

Date: 2026-09-26. The statement is
`selected_labelledTransverse_accepts_rankGood` at
`4a9dc01011265dcce62710eeb86b6a3136264939`.
It is not route-final. Theorem 1 and Corollary 2 are not claimed.
Full CMMSA stays partial.

The sample is `labelledTransverseLaw` on `transverseComplement` of one
question: one `starLaw` geometry with two leaves, a drawn center
functional, and a drawn functional on each leaf. `labelledTransverseAccepts`
restricts each leaf functional along that leaf's center inclusion and
requires equality with the drawn center functional. Rank-good is
`jointlyDirect` of that same geometry. The witness `r` is the mass of
`¬ jointlyDirect`, and `starLaw_bad_mass_lt_threshold` puts that mass
strictly below `S/2`. The fixed-star quantity
`2^{-4 (h − h / bOf nRows)}` is not this acceptance probability.
`transverseStarAcceptsCenter` remains in the file and is not this claim.

GCP replay on `quantyra-lean-builder-01` (`us-central1-a`,
`quantyra-lean-cert-20260915`, Lean `4.34.0-rc2`):
`lake build --old PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
exited 0 (3272 jobs). Receipt:
`evidence/gcp/satellite/gcp_actual_star_labelledTransverse_4a9dc01`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | GCP replay of the checks target exited 0 (3272 jobs) at `4a9dc01`. Axioms are `propext`, `Classical.choice`, `Quot.sound`. No `sorry`. |
| Proof-adversarial | GO | The inequality is `eventMass_accept_rankGood_ge` on `labelledTransverseLaw`. Both drawn leaves are tested by inclusion against the drawn center map. `r` is the bad-star mass and is strictly below `S/2`. |
| Complexity | GO-WITH-NOTES | One uniform geometry on `transverseComplement` plus both leaf charts. The subtraction uses the bad-star mass and is not a yes/no separation, an FP map, Theorem 1, or Corollary 2. `2^{-4 (h − h / bOf nRows)}` is not `Pr[accept]`. |
| Non-claims | GO | The module states the local inequality and does not claim Theorem 1, Corollary 2, P versus NP, an unconditional FP producer, route-final, or full CMMSA. README.md and MANUSCRIPT.md are unchanged. |
