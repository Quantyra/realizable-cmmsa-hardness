# Accepted-good-mass three-lens

Date: 2026-09-26. Proof commit `abd32bcc79483c1bcefaaf1e3085f7156ada2223`.
Scope: `selected_domainDraw_accepted_rankGood`. The measured law is
`uniformDomainTupleLaw` on ordered `DomainDraw` leaves of the question
center. `selectedLeafEquiv` is `domainDrawTupleExtensionEquiv` into
`coordinateCenterGrass`. Acceptance and `jointlyDirect` are that same
tuple. `leafT ≤ 2*h` is `leafT_le_two_mul_h`. `h ≤ blocks` is
`selected_hBlock_le_blocks`. This increment is not route-final.
Theorem 1 and Corollary 2 are not claimed.

The earlier table on `bb143dc` measured `starLaw` on random Grassmann
centers. That table is withdrawn.

GCP replay: `quantyra-lean-builder-01`, detached worktree at `abd32bc`,
`lake build --old PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`,
3262 jobs, exit 0.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | VM Lake exit 0 on the checks module. Axioms of the shipped theorems are `propext`, `Classical.choice`, and `Quot.sound`. |
| Proof-adversarial | GO | The law is the uniform `DomainDraw` tuple. Both events are the image under `domainDrawTupleExtensionEquiv` of that tuple at `coordinateCenterGrass`. Endpoint guards are lemmas. Bad mass is the fixed-center threshold pulled back by `extensionTuple_eventMass_eq_preimage`, not a `starLaw` average. |
| Complexity | GO | `w` only witnesses nonemptiness. The defect sits inside `¬ jointlyDirect`, whose mass is `< 2^{-(badExponent+1)}`. `q < successMargin / 2`. |
| Non-claims | GO | No Theorem 1, Corollary 2, `FP` map, or route-final claim. README and MANUSCRIPT are unchanged. |

Full CMMSA remains partial.
