# Tagged composed source to physical force

- Satellite source base: `fb5a2eb5cd3cecc55c8117d34bec44eb750240c3`; focused proof commit: `25d062a`.
- Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`. Local `gcloud.cmd` calls used `subprocess.CREATE_NO_WINDOW`.
- Isolated exact-source tree: `/tmp/cmmsa-target-r2`, with pinned package cache `/home/dfredriksen_quantyra_org/cmmsa-phasea-build-185df9d/.lake/packages` and absolute Lake `/home/dfredriksen_quantyra_org/.elan/bin/lake`.
- Terminal Checks build: `lake build PvNP.RealizableHardness.ActualTaggedComposedPhysicalSamplerChecks`, exit `0`, 3259 jobs. Full output: `checks.log`, SHA-256 `d32c3dc2283135e46ca39557d93c756e469a3cd5412a27642e6725ba2e846fbf`.
- Targeted `#print axioms` for presentation invariance, full-domain atom, exact score equality, legal event equivalence, and legal value transfer reported only `propext`, `Classical.choice`, and `Quot.sound`.

| Lean module | SHA-256 |
| --- | --- |
| `ActualTaggedTargetPresentationInvariant.lean` | `8fc3865ce3e3bbed6cf0ea6b135701367cca5535ac60ad2d69e7c1c78842238a` |
| `ActualTaggedComposedPhysicalSampler.lean` | `209a166b3425659cc541a9ee5cbe4a3185e51ed0fcd172b37cf358cbe3b0f999` |
| `ActualTaggedComposedPhysicalSamplerChecks.lean` | `a9dd97e6675b7c1325a2a7434cc33c3cbb5f2d7585434405ca53ddd0521a45e2` |

The explicit law samples an eligible ordered `U`, a transverse stored `K`, and independent uniform full domains `D_i`; its atom theorem gives the product of those three uniform weights. Independent uniform full-vertex representatives then define the fixed-table composed score. For every fixed center table `C` and arbitrary raw left table `T`, `composedTaggedScore_eq_orderedPhysicalMass` identifies that score exactly with the existing ordered tagged physical mass. The target presentation event is invariant at fixed full domains, and a legal left table makes the raw-label validity gate automatic.

`composedLegalValue` is the finite maximum over fixed legal left and center tables before the draw, with invalid left tables assigned zero. A value above `2^-q` extracts one fixed legal pair and forces the existing MZ high-density-`U` threshold for a selected full-domain table. This closes the modeled composed-source to physical-mass comparison for the same fixed tables. It does not establish the downstream MZ local decoder, the outer NO comparison, or Theorem 1; the numerical NO exponent is unchanged.
