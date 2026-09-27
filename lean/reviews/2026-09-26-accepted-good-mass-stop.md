# Accepted-good-mass inequality for the labelled transverse star

Date: 2026-09-26. Theorem 1 and Corollary 2 are not claimed.
The increment is not route-final. Full CMMSA stays partial.
README.md and MANUSCRIPT.md are unchanged. No new carrier, palette,
or conditional wrapper is opened.

## Inequality

`Pr[labelledTransverseAccepts ∧ jointlyDirect] ≥ Pr[labelledTransverseAccepts] − r`
with `r < S/2`, where `S = 2^{-E}` and
`E = badExponent nRows (hBlock L nRows)`, at
`selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
`h = hBlock L nRows`, leaf rank `2 * h`, center rank `leafT nRows h`,
and two leaves.

Lean theorem:
`selected_labelledTransverse_accepts_rankGood`.

## Same experiment

`labelledTransverseLaw` on `transverseComplement` of one question.
The geometry is one `starLaw` draw: `centerLaw` draws the center and the
two leaves are independent uniform extensions. The same draw carries a
center functional and one functional on each leaf. `labelledTransverseAccepts`
restricts each of those leaf functionals along that leaf's inclusion of the
center and requires equality with the drawn center functional. Rank-good is
`jointlyDirect` of that geometry. The bad-star event is its negation.

`r` is that bad-star mass. `starLaw_bad_mass_lt_threshold`, discharged at
these parameters, puts it strictly below `S/2`. The fixed-star conditional
`2^{-4 (h − h / bOf nRows)}` is not this acceptance probability.
`transverseStarAcceptsCenter` uses one canonical label and is not this claim.

## Build

`lake build --old PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
on `quantyra-lean-builder-01` exited 0 (3272 jobs) at
`4a9dc01011265dcce62710eeb86b6a3136264939`. Receipt:
`evidence/gcp/satellite/gcp_actual_star_labelledTransverse_4a9dc01`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.

## Three-lens

| Lens | Verdict |
|------|---------|
| Build/audit | GO |
| Proof-adversarial | GO |
| Complexity | GO-WITH-NOTES |
| Non-claims | GO |

The table is `lean/reviews/2026-09-26-accepted-good-mass-three-lens.md`.
The increment is not route-final.
