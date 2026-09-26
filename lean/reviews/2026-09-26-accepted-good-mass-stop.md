# Stop: same-experiment accepted-good mass

Date: 2026-09-26. This is outcome B. It is not route-final.
Theorem 1 and Corollary 2 are not claimed.

## Failed inequality

On one sample, at the selected parameters,

`Pr[accept ∧ rankGood] ≥ Pr[accept] − q` with `q < S/2`,

where `S = 2^{-E}` and `E = badExponent nRows (hBlock L nRows)`,
for `nRows` chosen by `selector (fun n => max (sourceHMin n) (n + 2)) L`,
with `leafT`, `leafK`, and `blocks` at that block height.

The sample must draw its center from `ActualSourceStarLaw.centerLaw`
and its leaves from `DomainDraw` of `coordinateCenterGrass` of that
drawn center. Acceptance and joint directness are events of that same
sample.

## Kill

`centerLaw` is the uniform law on `Grass V t`.
`DomainDraw` and `coordinateCenterGrass` are defined only for a
`QuestionCenter`. No theorem sends a `centerLaw` outcome to a
`QuestionCenter`.

`uniformDomainTupleLaw center` samples `DomainDraw` leaves of a center
supplied as a parameter. The center is not a draw from `centerLaw` in
that experiment. A witness `w` only shows the leaf carrier is nonempty.

`starLaw` does draw its center from `centerLaw`, and its leaves are
`Extension`s of that center. Those leaves are not `DomainDraw`s of
`coordinateCenterGrass` of the drawn center.

The two carriers are not one experiment, so the inequality is not
proved. No QuestionCenter–Grass identification, palette, or conditional
wrapper is opened after this stop.

## Three-lens

The tables that marked proof-adversarial and complexity `GO` for the
supplied-center `DomainDraw` theorem, and for the random-Grass `starLaw`
theorem, are withdrawn. Those lenses did not accept the required
experiment.

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | The supplied-center module builds. That build is not this inequality. |
| Proof-adversarial | INCOMPLETE | No review accepted a sample that draws the center and the `DomainDraw` leaves together. |
| Complexity | INCOMPLETE | Same gap. A nonempty leaf witness does not draw the center. |
| Non-claims | GO | README and MANUSCRIPT are unchanged. Theorem 1 and Corollary 2 are not claimed. |

Full CMMSA remains partial.
