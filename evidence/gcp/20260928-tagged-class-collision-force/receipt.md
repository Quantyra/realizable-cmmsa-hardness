# Tagged class-collision force comparison

- Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`.
- Exact source: satellite commit `b3f3741` plus the three SHA256-matched Lean files below, in isolated `/tmp/tagged-outer-r1`. Complete pinned package cache: `/home/dfredriksen_quantyra_org/cmmsa-phasea-build-185df9d/.lake/packages`.
- Terminal proof build: detached PID `11449`, exit `0`; `lake build PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound`, 3250 jobs.
- Terminal checks build: detached PID `11756`, exit `0`; `lake build PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBoundChecks`, 3251 jobs. Full output: `checks.log.gz`.
- All five exported theorems in Checks report only `propext`, `Classical.choice`, and `Quot.sound`.

| Lean file | SHA256 |
| --- | --- |
| `ActualTaggedPresentedSelection.lean` | `838b2b75dd69c9706b6e924df4d3ad3e0e661747f9f9bf486853cb55a593b793` |
| `ActualTaggedOrderedClassCollisionBound.lean` | `9de71b12e30d3464c5a2420a9845015a73723b00bb208f80d17addfdbb935ca4` |
| `ActualTaggedOrderedClassCollisionBoundChecks.lean` | `6747d288147a3a1b1d30267afdd7c5104de0be7eeb704ef3f7a79608c13c68d6` |

For each fixed eligible tagged question `q=(U,K)`, the conditional pair class-collision probability is exactly `1 / gaussian (2*J-t) (2*h-t)`. The collision probability among `k` independent conditional leaves is at most `choose k 2 / gaussian (2*J-t) (2*h-t)`, hence at most `(1/2)^J` when `t<=2*h`, `h<=J`, `2*J<=(2*h-t)*(2*J-2*h)`, and `k^2<=2^J`.

The same numeric bound holds for the concrete tagged `U/K/leaf` law's outer `taggedClassCollisionMass`. Consequently, for **every fixed** tagged center table `C` and raw vertex table `T`, there exists a **single global** representative choice `s` with `taggedPhysicalMass <= taggedSelectedMass + (1/2)^J`. The table quantifiers precede representative selection, matching the arbitrary-fixed-table comparison needed by the NO decoder.

This discharges the class-collision loss in that comparison and reduces the numeric NO-soundness gap by making its loss explicit. It does not bound the selected mass by the MZ NO decoder, prove the initial-vertex/clique-resampled-row ordered marginal, or certify Theorem 1. Those are separate remaining force steps. Review status: awaiting formal three-lens closeout.