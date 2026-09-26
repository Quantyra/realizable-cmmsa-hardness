# Accepted-good-mass three-lens

Date: 2026-09-26. Commit `bb143dc3f5e6fa77f6465658b041a16fe8c37978`.
Scope: `sameExperiment_accepted_rankGood` and
`selected_sameExperiment_accepted_rankGood` in
`ActualStarAcceptedGoodMass.lean`. This increment is not route-final.
Theorem 1 and Corollary 2 are not claimed.

GCP replay: `quantyra-lean-builder-01`, detached worktree at `bb143dc`,
`lake build --old PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`,
3261 jobs, exit 0. Log:
`evidence/gcp/satellite/gcp_actual_star_accepted_good_mass_20260926T182813Z/goodmass-build.log`.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | VM Lake exit 0 on the checks module, which imports the shipped theorems. Axioms are the standard Lean trio when printed by the checks file. |
| Proof-adversarial | GO | Bad event is `¬ jointlyDirect` on one `starLaw` tuple. `goodStar` is `accepts ∧ jointlyDirect` on that tuple. Equal fiber sizes make the cardinality sum a center average. Every center is strictly below `2^{-(E+1)}`, and `sum_lt_sum` keeps the average strict. `q` is the midpoint of the defect and half the margin. No `sorry`. The selected `QuestionCenter` only names the coordinate space. |
| Complexity | GO | Both masses are `eventMass` of one `starLaw`. The law factors as `centerLaw` times transverse extensions. The defect is `accept ∧ ¬ jointlyDirect`, inside `¬ jointlyDirect`. `q < successMargin E / 2` with `successMargin E = 2^{-E}`. The measured law is not `uniformDomainTupleLaw`. |
| Non-claims | GO | README and MANUSCRIPT are unchanged. The module states the inequality and says it does not prove Theorem 1, Corollary 2, or an `FP` reduction. `ROUTE_FINAL=NO`. |

Full CMMSA remains partial.
