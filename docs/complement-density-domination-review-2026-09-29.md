# Actual complement density domination

Status: bounded kernel-checked density comparison; conditional core certificate
and numerical NO soundness remain incomplete. Planning: S3126/S3132.

For every occurrence instance, copy count, eligible fixed U, arbitrary fixed
predraw tables C/T', and t <= 2h, h <= J, the actual `sideConditionalDensity`
is at most the uniform complement average of the existing ordinary
`ActualChangedAmbient8SBoundary.StarDensity`. Each complement uses deterministic
pullbacks of the same C/T' on the same observed full domains. No table is chosen
after its center or leaf tuple is sampled.

The fixed-center theorem retains the actual row-checked `fullAccepts` experiment
and transports its ordered leaf tuple by an exact equivalence. Dropping RHS
checks gives pointwise domination. Center and tuple reciprocal weights are
preserved by cardinal equivalences. The exact weighted-law identity factors
the original complement weight out of its existing center/leaf sums; the final
theorem joins this identity to the previously certified source complement law.
There is no sampler approximation or new loss, and no assertion that actual
acceptance equals restriction-only star acceptance. Class collision remains
upstream.

## Verification

The minimal scalar helper Lake target completed 674 jobs, exit zero (67319).
The fixed-center direct Lean check exited zero (72679), and its required direct
OLean export exited zero (93521) on the same source. The integrated bound direct
OLean export exited zero (32097), with only a `letI` style warning. Dedicated
Checks direct OLean export exited zero (26188), no warnings/errors. All four
exported density results print only `propext`, `Classical.choice`, and `Quot.sound`.
These are scoped direct kernel checks and exports, not a fresh full repository
rebuild or manuscript-wide certification.

| Source | SHA256 |
| --- | --- |
| ActualFiniteScalarSumReindex.lean | 5B34D19A49F99E30AE7278E1D12CC4740F3946E4E2FA4D5AB1F2E56AE3BCB216 |
| ActualTaggedComplementStarLeafMassBound.lean | B0F85BD4261289DA484B829B96C2AA49C783F1A2D1C73DD6AA230BBFFE20A9D5 |
| ActualTaggedComplementStarDensityBound.lean | ED7F7766252D76E57BFD063080CB94F9B6AA364BBF3C8417DBE86D1350C95A1D |
| ActualTaggedComplementStarDensityBoundChecks.lean | 026F1B539E0ED114267D397189952E7EF81E1CC74F8C270D90EC6DFC0AD3A61B |

## Three-lens review

| Lens | Verdict | Note |
| --- | --- | --- |
| Build/audit | GO | Scoped kernel checks/exports and standard axiom profiles |
| Proof adversarial | GO-WITH-NOTES | Actual law, exact weights and deterministic same-table transport; no blocking issue |
| Complexity theory | GO-WITH-NOTES | Correct averaged domination; collision upstream; no inverse or numerical NO claim |
| Non-claims boundary | GO-WITH-NOTES | Inequality wording matches theorem; no core certification claim |

Reviews were launched at top level by the root orchestrator. The complexity
reviewer also orchestrated Luna and supplied proof hints. This overlap is
disclosed; it is a role review, not independently authored verification.
The k=0 pointwise event may be vacuous, but ordinary fibers in the integrated
theorem are genuinely nonempty under its dimension guards. No high-density
complement existence, positive complement fraction, all-ambient inverse,
robust 8S, outer NO strategy, encoded runtime, or full Theorem 1 is proved here.
Existing S3126 wider-core review debt persists.

## Resource evidence and next step

Several attempts were controlled resource stops without proof diagnostics;
they are neither Lean failures nor passes. Historical 3.5 GiB was a prepared
diagnostic launch reserve and was incorrectly reused as a continuous-stop
heuristic. After checking its provenance, root explicitly set this run's guard
to launch at least 3.5 GiB free, sole direct compiler, and stop below 2.5 GiB.
This changed run orchestration, not repository policy or mathematical scope.
The 39102 and 57573 checks then returned actionable finite-reindex diagnostics;
the scalar-function congruence repair passed 72679. Local heartbeat limits were
reduced to 200000, not escalated. No other processes or system settings were changed.

Next: derive the actual high-density complement witness and exact selected
functional coefficient bounds needed by the inverse. Then prove the positive-rank
exact-nominal-budget hypercontractive bound and its common-center spectral/moment
consumer, all-ambient inverse, robust 8S, and outer NO assembly. The numerical
NO-soundness gap is unchanged. No push, release, or stronger public claim.
