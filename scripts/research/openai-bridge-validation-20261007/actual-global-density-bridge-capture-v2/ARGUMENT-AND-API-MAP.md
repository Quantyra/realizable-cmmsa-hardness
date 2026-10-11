# Actual global density to one ordinary complement star ? v2

Offer version: v2, successor to the immutable v1 capture.

Status: static Lean translation candidate only. This offer has not been run
through Lean/Lake, native checks, GCP, or review. It proves only the
conditional finite-averaging implication stated below; it does not construct
the global density, the fixed tables, or a source instance.

## Exact public target

`exists_complement_with_star_density_ge` fixes one `I`, `copies`, `U`, center
table `C`, and leaf table `T'`. Under `ht : t <= 2*h`, `hh : h <= J`, and the
single input premise

```lean
e <= sideConditionalDensity I copies U t h k C T'
```

it returns an actual complement `A` such that `e` is at most the ordinary
`StarDensity` of the deterministically transported `C` and `T'` on that same
complement. The target does not condition the law on acceptance and does not
select new tables after seeing `A`. It introduces no positivity premise on
`e` and no stronger score premise.

`transportedStarDensity` derives its center and leaf nonemptiness internally.
The dimension identity is `sideComplement_finrank ... A : finrank A.1 = 2*J`;
the ordinary leaf width is `2*h`, with `h <= J` supplying its upper bound.

## Proof dependency map

1. `complementFullAcceptMass` is exactly the `A`-conditional full-acceptance
   mass in `ordinaryComplementStarDensity`, with the outer uniform-complement
   factor removed. `ordinaryComplementStarDensity_eq_average_fullMass`
   distributes that outer factor over the finite sum.
2. `transportedStarDensity_reindexed` uses
   `centerInComplementEquiv` and `ordinaryStarLeafEquiv` to put the ordinary
   star sum on the actual center and ordinary-leaf carriers. The equivalences
   preserve the same event's uniform mass and its cardinal normalizers.
3. `complementFullAcceptMass_le_transportedStarDensity` applies
   `actual_implies_ordinary_star_accepts` pointwise and sums with nonnegative
   uniform weights. It establishes an inequality, not equality: dropping
   the actual row-right-hand-side checks can enlarge the event.
4. `exists_complement_with_star_density_ge` rewrites the global score using
   `sideConditionalDensity_eq_ordinaryComplementStarDensity`, applies the
   per-complement inequality, and normalizes the finite average. The finite
   pigeonhole step is `Finset.exists_le_of_sum_le` after multiplying by the
   positive complement cardinal.

## V2 static repair details

- Replaced the non-Lean `sum` token with the actual `?` binder notation.
- Every use of the phantom parameters of `transportedStarDensity` and
  `complementFullAcceptMass` now specifies `(t := t) (h := h) (k := k)`.
  This fixes the intended sampled star count `k` to the same `k` used by
  `sideConditionalDensity`.
- In `ordinaryComplementStarDensity_eq_average_fullMass`, the proof expands
  the outer complement scalar successively through the complement, center,
  and leaf sums using three `Finset.mul_sum` rewrites. The final scalar
  reassociation is discharged by `ring`.
- In the pigeonhole step, `hconst` explicitly evaluates the sum of the
  constant threshold using `Finset.sum_const`, `Finset.card_univ`, and
  `nsmul_eq_mul`. The proof installs `hsideComp` as a local `Nonempty`
  instance before using `Finset.univ_nonempty`, then converts the card-times-
  threshold inequality to the exact sum inequality expected by
  `Finset.exists_le_of_sum_le`.
- Static source inspection confirmed that pinned `StarDensity` weights are
  left-associated `uniform center * uniform leaves * indicator`, matching the
  reindexed summand's multiplication order. The pinned
  `ActualOrdinaryStarWeightedSelection.exists_weighted_matching_functional`
  uses the same `exists_le_of_sum_le` / `Finset.univ_nonempty` pattern, and its
  constant-sum normalization uses the same three lemmas listed above.

These are source-level repairs only; no Lean elaboration or compilation was
performed.

## Nonempty carriers and denominators

`t <= 2*h` and `h <= J` give `t <= 2*J`. The imported
`taggedCenterOver_nonempty` and `centerToSide` yield a `SideCenter`. The exact
`side_complements_over_card` formula gives a positive complement-over-center
fiber, hence a nonempty `SideComplement` and a nonzero outer denominator.
For every complement, `centerInComplement_card` gives the center fiber. The
ambient dimension `2*J` and width `2*h` make every extension/leaf carrier
nonempty by `extension_nonempty`; `ordinaryStarLeafEquiv` transports that
nonemptiness. These are derived facts, not theorem premises.

## Exact upstream pins

All listed member hashes were recomputed from Full113's
`input-archive.tar.gz`, SHA256
`BE67B48A7D6AA2745A1D28B99953E29B5764686EECFE4EDCFA01908872DE7EC2`.

| Source member | SHA256 |
|---|---|
| `ActualTaggedComplementIncidence.lean` | `d51ca831411a7d9ef361f46adabf87c1517bb3f04b7804355cd855b1dd9cdac5` |
| `ActualTaggedComplementStarDensityBridge.lean` | `ba424e93e53b1e898353f6c6ae2ea42d995a31a8f7d352632e471674bb6dbe4b` |
| `ActualTaggedMZSideDraw.lean` | `b2cce2fc8f7cfbc646a70efbb5760711d9f5f89b371842d6ed5512e93501dfab` |
| `ActualOrdinaryStarSelection.lean` | `04e4ec58cfc28ef1361a42d6040be7ef9c104de543f18cadd6794bafbbfb9758` |
| `ActualBinaryGrassmannIncidence.lean` | `d4f36030331a437c320d35e131308b6872b108689357a75fe0dcfa54c9991f96` |
| `ActualTaggedOrderedSampleNonempty.lean` | `89a9c9f582cf8e5445706c4d74e0951e8c8cc349029d4014b90e8433791da4cf` |
| `ActualSourceStarLaw.lean` | `dc4ec18dcf630a02207318690d64cda672e0dacbc72dcd34c438baaaf883da11` |
| `ActualChangedAmbient8SBoundary.lean` | `83ae836baacb7f71bbe801743740f657ea84931488a46a0209195e3c64854ad2` |
| `ActualFiniteLaw.lean` | `8c39a4ba4045f4f6d31c92cedda4c5b46f50a48e4f654bf517f90e08cfd0fa32` |

## Remaining boundary

This theorem only starts from the actual global rational side-density lower
bound. It neither proves that bound nor invokes the selected numeric
parameters, the bad-mass cutoff, or the weighted functional theorem. Those
are separate downstream composition steps.
