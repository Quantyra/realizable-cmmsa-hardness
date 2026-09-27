# Accepted-good-mass three-lens

Date: 2026-09-26. Theorem: `selected_presented_starAccepts_rankGood`.
The sample is `physicalPresentedLaw`. Acceptance is `starAccepts` on the
presented rank-`2h` leaves. Rank-good is `jointlyDirect` of that same star.
`physicalPresentedLaw_center` charges the center by `centerLaw`.
This is not route-final. Theorem 1 and Corollary 2 are not claimed.
Full CMMSA stays partial.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Local `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks` exited 0 (3272 jobs). Axioms of the theorem: `propext`, `Classical.choice`, `Quot.sound`. GCP replay of this theorem is a separate receipt. |
| Proof-adversarial | GO | `lean/reviews/2026-09-26-presented-starAccepts-proof-adversarial.md` names `selected_presented_starAccepts_rankGood`. |
| Complexity | GO-WITH-NOTES | `lean/reviews/2026-09-26-presented-starAccepts-complexity.md` names `selected_presented_starAccepts_rankGood`. The bound is the gap below half the success margin. It is not an FP reduction. |
| Non-claims | GO | `lean/reviews/2026-09-26-presented-starAccepts-non-claims.md` names `selected_presented_starAccepts_rankGood`. Public `README.md` and `MANUSCRIPT.md` are unchanged. |

Review debt for route-final use: the manuscript producer, Theorem 1, and Corollary 2 remain open.
