# Tagged fixed-table canonical comparison

- Source: satellite commit `f97a1d1ff5b126deb217402269af2c4278c940fe`.
- Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`; local `gcloud` calls used Python `subprocess.CREATE_NO_WINDOW`.
- Exact-source isolated checkout: `/tmp/cmmsa-mz-0fee269`, built after the main Lean file was SHA256-matched to the committed `f97a1d1` blob. The Checks file came unchanged from the `0fee269` archive and has the same SHA256 as `f97a1d1`.
- Detached terminal build: PID `3352`, exit marker `0`, `lake build PvNP.RealizableHardness.ActualTaggedCanonicalNoComparisonChecks`, `Build completed successfully (3253 jobs)`; full output in `checks.log`.
- `#print axioms tagged_physical_le_canonical_plus_collision`: only `propext`, `Classical.choice`, `Quot.sound`.

| Lean file | SHA256 |
| --- | --- |
| `ActualTaggedCanonicalNoComparison.lean` | `a6b134c247b90a9393e68c6169f778f441bb01c937d0cf4ddd67c7b42a1810c5` |
| `ActualTaggedCanonicalNoComparisonChecks.lean` | `d79a58365691afce85a678561603dc1cc59658178e1e692bdeb245dfc7e6ea0f` |

The theorem quantifies over every fixed center table `C` and raw tagged vertex table `T`. Under the explicit numeric guards `t ≤ 2h`, `h ≤ J`, `2J ≤ (2h-t)(2J-2h)`, and `k² ≤ 2^J`, it chooses one full-domain table `T'` before the star draw and proves physical acceptance mass for the normalized uniform eligible-set `U`, uniform conditional `K`, and independent uniform conditional leaves is at most canonical `taggedAccepts` mass for `T'` plus `2^-J`. This composes the prior class-collision theorem with the exact selected-event/canonical-event bridge; no decoder conclusion is assumed.

**First missing source-law theorem:** `orderedStarLaw I copies J hcenter hleaf = taggedSampleLaw I copies hcenter hleaf` for the same `J,t,h,k`, or the corresponding equality of canonical acceptance masses. The existing `orderedGood_pushforward` proves only the ordered-U first marginal. The full dependent `K` and independent-leaf pushforward equality was attempted but did not compile; no draft remains in the committed source. Until this is proved, the new theorem must not be described as the manuscript's full ordered-star comparison. After that bridge, the source-derived MZ Theorem 4.2 local decoder remains missing: high conditional inner-test density for the fixed canonical table must yield `a+c ≤ 10m/ρ`, favorable uniform advice mass at least `2^-6h²`, and conditioned agreement at least `2^-2(1-1000ρ²)h/5`, with the side conditions and transversality charges stated in `MANUSCRIPT.md`.

The increment connects the explicit collision charge to canonical acceptance but does not further lower the numerical NO-soundness gap or certify Theorem 1.
