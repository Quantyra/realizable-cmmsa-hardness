# Complement pointwise verification handoff

Later same-day update: the formerly pending integrated density comparison was
kernel-checked and reviewed in `complement-density-domination-review-2026-09-29.md`.
The unverified-bound and resource observations below describe the earlier handoff;
the analytic inverse, robust 8S and full core remain incomplete.

Status: pointwise proof built and three-lens reviewed with notes; integrated
density comparison remains incomplete. Planning ownership: S3126/S3132, with
existing S3126 review debt. This is a progress handoff, not route-final closeout.

Luna implemented `actual_implies_ordinary_star_accepts` in
`lean/PvNP/RealizableHardness/ActualTaggedComplementStarDensityBridge.lean`.
For fixed eligible U, complement A, center Kc, and actual ordinary leaf tuple,
actual `fullAccepts` implies ordinary `StarAccepts` of the same transported
predraw C/T' tables. Only the copied-row RHS checks are dropped. The center
and full-leaf domain equalities are proved; no decoder or inverse is assumed
to obtain this pointwise implication.

Verification: direct Lean session 81746 exited zero. The focused Lake target
`PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge` completed
3262 jobs successfully. Direct Checks session 87619 exited zero and printed
only `propext`, `Classical.choice`, and `Quot.sound` for the exported implication.

Frozen SHA256: bridge
`ADA143BA67BA5F4FCA40B080D79D57751B9961F56A7A6D3967A5642ED36FB398`;
Checks `2FE566CF7CFF8A9EEE4D3C4E6B14E7E8A11F78AA709457203C076745A8F8F7E8`.
The exact source pair is accepted for focused local tracking after top-level
review. No push, release, or claims expansion is authorized by this acceptance.

The new `ActualTaggedComplementStarDensityBound.lean` remains unverified.
Session 74934 reached the pointwise leaf-sum comparison but failed dependent
center elimination. The current revision replaces that final cast with a
scalar `starMass` and center-equivalence reindex. Subsequent resource-controlled
interrupts, including 51353 at 3209960 KiB available RAM, returned no proof
diagnostics. They are not Lean proof failures or successful checks. No compiler
remained active at handoff; latest independent memory read was 5205048 KiB free.

| Lens | Verdict | Scope |
| --- | --- | --- |
| Build/audit | GO for pointwise implication | Focused target and direct Checks; standard axioms |
| Proof adversarial | GO-WITH-NOTES | Exact domain and pointwise evaluation transport; no blocking issue |
| Complexity theory | GO-WITH-NOTES | Same predraw tables and correct implication direction; role overlap disclosed |
| Non-claims boundary | GO-WITH-NOTES | Pointwise wording bounded; integrated density and core excluded |

The top-level complexity reviewer also orchestrated the implementation and
provided proof hints. This is a disclosed role review, not independently
authored verification. Empty typed carriers and `k=0` may make a pointwise
event vacuous; no positive-mass inference is made. Integrated density, analytic
inverse, robust 8S, numerical NO soundness, and core Theorem 1 are explicitly
outside this acceptance. Existing S3126 review debt persists for the wider core.

Next: separately compile the scalar density comparison, prove its exact weighted link to the existing
`ordinaryComplementStarDensity`, and audit its axioms. Then feed the actual
ordinary density into the already present weighted selection theorem (7293d45),
prove its required ratio/exponent bounds, and continue positive-rank analytic
inverse and changed-ambient robust 8S. Encoded reduction/runtime and final core
Theorem 1 remain open. The numerical NO-soundness gap is unchanged.

OpenCode's prescribed launch failed with invalidated OAuth; proof execution
used the user-authorized collaboration Luna fallback. The parent orchestration
agent initially reported model capacity failure; it subsequently recovered and
launched the three top-level reviews. No nested review substituted for them.
