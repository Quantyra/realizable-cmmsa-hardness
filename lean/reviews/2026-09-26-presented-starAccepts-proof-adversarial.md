# Presented starAccepts proof-adversarial review

**Theorem:** `selected_presented_starAccepts_rankGood`

**Verdict: GO**

Date: 2026-09-26. Module: `lean/PvNP/RealizableHardness/ActualStarAcceptedGoodMass.lean`. This note does not call the result Theorem 1, Corollary 2, or route-final.

The measured sample is one point of `physicalPresentedLaw`: a transverse star, the rank-`2 * hBlock` `PresentedLeaf` of each extension via `physicalPresentedLeaf` / `presentedOfTransverseLeaf`, and source and query `LeafLabel` coordinates on those leaves. `physicalPresentedLaw_center` charges the Grass center by `centerLaw`. Acceptance in the statement is `starAccepts` on those coordinates (`labelledAccept_eq_starAccepts`). Rank-good is `jointlyDirect` of that same star. There is no constant fibre, supplied center, argument table, or forall-draw exists-table witness. `labelledAccept` is not proved for every sample and is not replaced by `Finset.univ`.

`E = badExponent nRows (hBlock L nRows)`. `physicalPresented_bad_mass_eq` identifies the labelled `¬ jointlyDirect` mass with the `starLaw` bad mass, and `starLaw_bad_mass_lt_threshold` puts that mass strictly below `successMargin E / 2`. The accepted-bad event sits inside that bad event, so `Pr[accept] - Pr[accept ∧ rankGood]` is strictly below the same half-margin. The exhibited `q` is the midpoint between that loss and the half-margin. That monotonicity is the required inequality; the numerical value of `Pr[accept]` is not required.

Full CMMSA stays partial.
