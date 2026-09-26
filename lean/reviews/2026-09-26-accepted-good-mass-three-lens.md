# Accepted-good-mass three-lens

Date: 2026-09-26. Outcome B. The required inequality is not this table's theorem.
`selected_transverseLeaf_accepted_rankGood` measures `starLaw` on extension
tuples. `transverseLeafAccept` holds for every sample, so the proved bound
has acceptance mass 1. The physical acceptance event is `starAccepts`.
See `lean/reviews/2026-09-26-accepted-good-mass-stop.md`.
This is not route-final. Theorem 1 and Corollary 2 are not claimed.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Local `lake build` and the GCP replay at `4d346bb` exited 0. That build is the `jointlyDirect` bound, not the physical `PresentedLeaf` acceptance inequality. |
| Proof-adversarial | NO-GO | Acceptance is proved for every sample and set equal to `Finset.univ`. |
| Complexity | NO-GO | The measured carrier is `starLaw` on `Extension`, not a `PresentedLeaf` law. `presentedOfTransverseLeaf` is not the sample space. |
| Non-claims | INCOMPLETE | No separate non-claims note. The stop does not claim Theorem 1, Corollary 2, or route-final. |

Full CMMSA remains partial.
