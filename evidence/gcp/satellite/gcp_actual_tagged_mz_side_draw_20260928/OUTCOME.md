# Fixed-U MZ side draw check

Source commit: `260d33095ed22680d0a43b79febe2ac0ac0f483c` (before this receipt).
Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`.
Remote isolated checkout: `/home/dfredriksen_quantyra_org/cmmsa-mz-side-d17b6ba` with the two source files copied from the above commit. The checkout used the pinned package cache at `~/cmmsa-phasea-build-185df9d/.lake/packages`.

## Source SHA256

| File | SHA256 |
| --- | --- |
| `lean/PvNP/RealizableHardness/ActualTaggedMZSideDraw.lean` | `B2CCE2FC8F7CFBC646A70EFBB5760711D9F5F89B371842D6ED5512E93501DFAB` |
| `lean/PvNP/RealizableHardness/ActualTaggedMZSideDrawChecks.lean` | `4F524AC40E3454521D38E73BF7134E23CBBF1F350D8C8E27806E40AB4D424927` |

## Terminal verification

Executed in the remote checkout:

```sh
~/.elan/bin/lake build PvNP.RealizableHardness.ActualTaggedMZSideDrawChecks
```

The captured terminal result exited `0` and ended with `Build completed successfully (3260 jobs).` It reported `Built PvNP.RealizableHardness.ActualTaggedMZSideDraw` and `Built PvNP.RealizableHardness.ActualTaggedMZSideDrawChecks`. The source also passed a direct `~/.elan/bin/lake env lean lean/PvNP/RealizableHardness/ActualTaggedMZSideDraw.lean` check with exit `0` before the targeted build. No full terminal log was saved as a separate file; these are the captured terminal results from the run.

The Checks module printed the following axiom dependencies for each declaration below: `[propext, Classical.choice, Quot.sound]`.

- `centerEquivSide`
- `leafEquivSide`
- `taggedDrawEquivSide`
- `taggedAccepts_iff_sideAccepts`
- `conditionalCanonicalDensity_eq_side`
- `composedLegalValue_gt_forces_side_threshold_U`

The builder stop command exited `0`; a subsequent instance description returned `TERMINATED`.

## Claim boundary

This proves the fixed-U side-conditioned draw/event/density identification and transfers the composed-value conclusion to the exact side-test `8S` threshold. It does not prove the MZ decoder or NO-soundness. The MZ Lemma 4.1 pseudorandom hyperedge bound remains the first missing analytic theorem.
