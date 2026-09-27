# Accepted-good-mass three-lens

Date: 2026-09-26. Outcome B. The terminal record is
`lean/reviews/2026-09-26-accepted-good-mass-stop.md`.
`selected_presented_starAccepts_rankGood` is not the required inequality.
This is not route-final. Theorem 1 and Corollary 2 are not claimed.
Full CMMSA stays partial.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks` exits 0. The checks file cites `starLaw_bad_mass_lt_threshold` only as an input, not as the claim. |
| Proof-adversarial | NO-GO | On the uniform law over label triples of one fixed equal-domain star, rank-good is empty and `Pr[accept] = 2^{-2·leafT} > S/2`. |
| Complexity | NO-GO | That probability is the law of the whole sample space, not `Pr[equal domain]` times a conditional probability. `agreementExponent_lt_badExponent` checks the exponent. |
| Non-claims | INCOMPLETE | No separate non-claims review of the stop. The stop text does not claim Theorem 1, Corollary 2, or route-final. |
