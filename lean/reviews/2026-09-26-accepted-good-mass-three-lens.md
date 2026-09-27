# Accepted-good-mass three-lens

Date: 2026-09-26. The failure claim is withdrawn. The record is
`lean/reviews/2026-09-26-accepted-good-mass-stop.md`.
`selected_presented_starAccepts_rankGood` is not the required inequality.
This is not route-final. Theorem 1 and Corollary 2 are not claimed.
Full CMMSA stays partial. The inequality is not proved and is not refuted.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks` exits 0. The checks file cites `starLaw_bad_mass_lt_threshold` only as an input, not as the claim. |
| Proof-adversarial | NO-GO | The fixed-star value `2^{-2·leafT}` is not `Pr[accept]` on the joint source law. Disjointness does not refute the inequality when that mass sits below `S/2`. |
| Complexity | NO-GO | On independent extensions of one center, `Pr[accept] ≤ 1 / gaussian(2 * J - t, leafK)`, and that count exceeds `2^{E + 1}`. |
| Non-claims | INCOMPLETE | No separate non-claims review of the stop. The stop text does not claim Theorem 1, Corollary 2, or route-final. |
