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

Withdrawn as a completion of the required experiment. The center in
`selected_domainDraw_accepted_rankGood` is a parameter, not a draw from
`centerLaw`. See `2026-09-26-accepted-good-mass-stop.md`.

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | The module builds. That is not the joint experiment. |
| Proof-adversarial | INCOMPLETE | A supplied `QuestionCenter` does not draw the center. |
| Complexity | INCOMPLETE | A nonempty leaf witness does not draw the center from `centerLaw`. |
| Non-claims | GO | README and MANUSCRIPT are unchanged. Theorem 1 and Corollary 2 are not claimed. |

Full CMMSA remains partial.
