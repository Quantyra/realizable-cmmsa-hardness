# Tagged ordered full-law force bridge

- Source commit: `b96387ba0a0119cccc5f048a63dd7b4924a16687`.
- GCP builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`. Local `gcloud.cmd` child processes used Python `subprocess.CREATE_NO_WINDOW`.
- Isolated exact-source checkout: `/tmp/cmmsa-ordered-force-r1`, populated from the parent HEAD archive plus the new source. Both final files were uploaded after source editing. Their SHA-256 values matched the committed local files byte for byte.
- Detached final Checks build: PID `4438`, `/tmp/cmmsa-ordered-force-r3.exit=0`; `lake build PvNP.RealizableHardness.ActualTaggedOrderedFullLawForceChecks` completed successfully, 3254 jobs. Full remote output: `/tmp/cmmsa-ordered-force-r3.log`.
- `#print axioms` for both `orderedStarLaw_eq_taggedSampleLaw` and `ordered_physical_le_canonical_plus_collision`: only `propext`, `Classical.choice`, `Quot.sound`.

| Lean file | SHA-256 |
| --- | --- |
| `ActualTaggedOrderedFullLawForce.lean` | `a09a2cc8e9b4dad48a10815890e6e42eb20ed830347ab925e759bbe4cee91c69` |
| `ActualTaggedOrderedFullLawForceChecks.lean` | `f438847ec7d4ab41c907f2d708f1e990e76833fd4133c1462adcfa6c37ce9e48` |

`orderedStarLaw_eq_taggedSampleLaw` proves the full dependent pushforward: uniform eligible ordered `U`, then uniform conditional stored `K`, then independent uniform conditional leaves has exactly the `taggedSampleLaw` distribution after forgetting row order. The proof uses the established exact eligible-row marginal and transports the same `K`/leaf kernel; the `K` selected for a sample is retained.

`ordered_physical_le_canonical_plus_collision` applies this equality to the prior fixed-table comparison. For every fixed center table `C` and arbitrary fixed raw tagged vertex table `T`, under explicit nonempty-fiber and numeric collision guards, it chooses one canonical full-domain table `T'` before the star draw. Ordered-source physical acceptance is at most canonical acceptance for `T'` plus `2^-J`.

This closes the ordered-to-eligible-set full-star source-law gap identified in the prior canonical comparison receipt. It does **not** prove the manuscript's initial-vertex/clique-resampled `U'` marginal, the MZ local decoder from canonical acceptance, the outer NO bound, or Theorem 1. The numerical NO-soundness bound is unchanged; the result makes the existing `2^-J` collision comparison applicable to the ordered-star source.
