# Actual tagged-question retained mass: complexity/manuscript review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for source-preserving tagged-copy padding (S3138)  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment correctly completes the finite retained-mass arithmetic for the actual post-regularization tagged row universe. For

```text
K = actualPaddingCopies J T = 1 + T * (157 J(J-1)),
```

positive `T` and a nonempty actual source imply

```text
actual tagged bad mass <= 1/T.
```

When `T >= 4`, the bad mass is at most `1/4`, the complementary good mass is at least `3/4`, the good event has positive cardinality, and its reciprocal mass is at most `4/3` and strictly below `2`. These are force-bearing conclusions: they discharge the manuscript's positive-retained-event and factor-two conditioning-denominator arithmetic once `T` has been chosen to meet the manuscript tolerance.

The increment does not itself make that choice from the manuscript parameter `tau`. No theorem mentions `tau` or proves `1/T <= tau/100`. It also does not define the conditioned distribution, prove the ordered-to-unordered legitimate-question law, establish the clique-resampling marginal, or construct the final polynomial-time randomized reduction. Source-preserving tagged-copy padding (S3138) therefore remains active.

## Frozen artifacts and certification evidence

| Artifact | Reviewed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionRetainedMass.lean` | `22F98B1FF1F84D0BED94744A62873A933C7B531EA310DA953D01B5FBA1581E91` | Exact requested frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionRetainedMassChecks.lean` | `9289DD63BEC7798158DF36D7E71D2C0E9365EB34401955C45B6FDF4C7177A2DB` | Exact requested frozen Checks source. |
| `research/evidence/2026-09-15-actual-tagged-question-retained-mass-fresh-run/artifact-hashes.txt` | `3D62FA741B1CC5AE6B8704D52444621059F06063B6812889FF2765D9A2C4E5D1` | Exact requested certified evidence manifest payload; its digest is recorded by `artifact-hashes-manifest.sha256`. |

The evidence records direct Lean main and Checks exits `0/0`, source stability, no preexisting target objects, and fresh object hashes `4BF0B86E...AB6` and `85B12CFC...64B`. The target was seeded from the prior certified actual-count dependency target while excluding the two reviewed target artifacts. This certifies a target-fresh main-and-Checks increment against recorded dependencies; it is not a from-zero project rebuild, and the provenance explicitly records `no_lake_build=true`.

The forbidden scan reports no `sorry`, `admit`, `native_decide`, or user `axiom`. The declared axiom profile is limited to `propext`, `Classical.choice`, and `Quot.sound`. The Checks file pins all definitions and theorems and exercises `J=0`, `J=1`, and a positive-good-cardinality case at `J=2`. Those fixtures are useful boundary checks; the universally quantified theorems carry the substantive coverage.

The manuscript consumer inspected was `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`, especially lines 1137-1176.

## What the theorem bundle proves

`actualTaggedGoodQuestions` and `actualTaggedBadQuestions` partition the full finite carrier

```text
Fin J -> (Fin K x I.RowId)
```

according to `GoodOrderedQuestion` for the support of `(Finite3LinSource.ofActual I).taggedCopy K`. The normalized rational masses use the cardinality of that full function space. The hypotheses `0 < K` and `0 < m` establish a positive denominator because the actual row universe is nonempty when `m` is positive.

The first theorem specializes the previously certified tagged conflict bound to the actual conflict-fibre constant `157`:

```text
bad mass <= 157 J(J-1) / (K * I.rows.length).
```

For `A = 157 J(J-1)` and `K = 1 + T A`, positive `m` gives `I.rows.length >= 1`, hence

```text
A T <= (1 + T A) * I.rows.length.
```

Cross multiplication by the positive denominators yields `bad mass <= 1/T`. This remains valid in the boundary cases `J=0` and `J=1`, where `A=0`, `K=1`, and the bad mass is zero. The extra `1` in the copy count ensures positivity without a separate zero-coefficient branch.

The remaining conclusions follow cleanly:

- `T >= 4` gives `1/T <= 1/4`, so bad mass is at most `1/4`.
- Exact finite complementation gives `good mass = 1 - bad mass`.
- Therefore good mass is at least `3/4`.
- Since the full carrier has positive cardinality, positive rational good mass implies the good finset has positive cardinality.
- Taking reciprocals of the positive good mass gives `1/good mass <= 4/3 < 2`.

No probabilistic independence is invoked in these last steps. The only law represented here is uniform counting on the already certified independently tagged ordered-tuple carrier.

## Manuscript dependency discharged

The manuscript says that the probability `a` of a discarded illegitimate tuple can be made at most `min(tau/100,1/4)` by disjoint-copy padding, and that conditioning then costs at most a factor two. The current increment now proves the following exact middle portion of that claim for the actual tagged semantic source:

```text
T >= 4
  => bad mass <= 1/4
  => good mass >= 3/4 > 0
  => 1/good mass <= 4/3 < 2.
```

Thus the conditioning event is nonempty and its normalization denominator is quantitatively safe. If the manuscript's `a` is instantiated as the exact actual tagged bad mass, the proved complement identity identifies

```text
1/(1-a) = 1/good mass.
```

The formal `4/3` bound is stronger than the manuscript's advertised factor two. Together with the separately certified generic tagged-copy optimum/value preservation and independent tagged-tuple law, this closes the semantic counting and denominator part of the copy-padding route. It does not close the encoded-producer or conditioned-law parts of that route.

## Missing `tau` carrier and quantifier order

The manuscript needs both inequalities

```text
bad mass <= tau/100
bad mass <= 1/4.
```

The reviewed source proves only `bad mass <= 1/T` and the second inequality under `4 <= T`. For rational `tau > 0`, the missing route theorem should choose an explicit natural number satisfying

```text
4 <= T
100 <= tau * T,
```

for example a ceiling-based `T >= max(4, ceil(100/tau))`, and then prove

```text
bad mass <= 1/T <= min(tau/100, 1/4).
```

Strict positivity of `tau` is essential; `tau=0` admits no finite `T` for the intended inequality. The theorem should preserve the manuscript's quantifier order: `m, xi, h, J, beta` and then the desired positive constant `tau` are fixed before `T` and `K`. Since these are fixed independently of input length, hardwiring their values can be compatible with the manuscript's fixed-parameter polynomial-time claim. The current noncomputable semantic definitions prove neither that uniformity statement nor any encoded size/runtime bound. A later producer must show that the chosen constant `K=1+157T J(J-1)` is represented and applied by the canonical source transformation with polynomial output size and all-word polynomial running time.

The theorem also uses `0 < m` as its concrete nonempty-source premise. The final reduction must prove this for every encoded instance reaching the route or give a polynomial-time small/empty-instance branch. It cannot leave the probability denominator to Lean's totalized division convention.

## Conditioned distribution and nonuniformity

The positive-cardinality theorem licenses defining a conditional law, but no conditional measure or sampler is defined here. A downstream theorem still has to prove, for every failure event `F`, the finite-law inequality

```text
Pr[F | Good] <= Pr[F] / Pr[Good] <= (4/3) Pr[F] < 2 Pr[F].
```

The present reciprocal inequality is the numerical denominator input, not the event-level conditioning theorem.

Conditioning the uniform tagged ordered-tuple law on tagged goodness is uniform over good tagged ordered tuples. It is generally **not** uniform after projection to the uncopied base-row tuple. For a fixed base tuple, the number of retained tag functions is the number of proper `K`-colourings of its position-conflict graph. Different base tuples can have different conflict graphs and therefore different retained-fibre sizes. In particular, a base-conflicting tuple can survive by assigning different tags to its conflicting positions. The downstream proof must not project the conditioned law to the original base game and call that projection uniform.

The safe consumer is the copied tagged universe itself. To match the manuscript's uniform legitimate `J`-equation-set law, the route must still prove:

1. conditioning the ordered tagged carrier gives the exact uniform law on `actualTaggedGoodQuestions`;
2. `GoodOrderedQuestion` supplies injectivity and is permutation invariant, so every legitimate unordered `J`-set has the same `J!` ordered fibre;
3. the ordered-to-finset pushforward is therefore uniform over legitimate tagged equation sets;
4. the actual star construction, transverse-space choices, equivalence classes, and clique-resampling kernel preserve that uniform legitimate-set law.

The manuscript's sentence that a uniform representative inside an equivalence class preserves the marginal requires an actual stationarity or equal-fibre argument for the concrete kernel. Equal dimensions and equal numbers of transverse extensions must be proved in the same distributional model. They do not follow from retained mass or from the reciprocal bound.

## Final randomized-reduction boundary

Positive retained mass makes rejection sampling mathematically plausible and gives expected trial count at most `4/3`. Expected polynomial time alone does not automatically supply the manuscript's bounded-random-bit, worst-case polynomial-time encoded reduction. The final construction needs an explicit sampler contract. Viable routes include exact enumeration of the good carrier when fixed `J` makes `N_outer^J` polynomial, or a bounded rejection procedure with its failure event charged to the reduction's error budget. Either route must specify rational sampling, runtime, seed length, malformed-input behavior, and the distributional distance or exactness used by the completeness and soundness arguments.

Beyond that sampler, this increment proves no actual-star acceptance theorem, RHS functional/minimal transport, rational formula-table compiler, YES/NO mean bounds, FP `SeededMap`, Real/Rat probability bridge, finite empirical-list concentration step, learning reduction, or headline randomized many-one hardness theorem. The manuscript's allowed parameter nonuniformity—one uniform polynomial-time reduction for each fixed leaf bound, without a common exponent as the fixed parameters vary—does not excuse omission of an explicit machine and polynomial bound for each fixed parameter choice.

## Route verdict

Source-preserving tagged-copy padding (S3138) may record the following as discharged at the frozen semantic level:

- actual normalized tagged bad mass bounded by `1/T` for positive `T` and `m`;
- the quarter bound for `T >= 4`;
- exact good/bad complementation;
- good mass at least `3/4` and positive good cardinality;
- conditioning reciprocal at most `4/3` and strictly below `2`.

S3138 must remain **Active** for the explicit positive-`tau` choice of `T`, the joint `min(tau/100,1/4)` theorem, the fixed-`K` encoded producer and complexity proof, the conditioned tagged law, ordered-to-subset transport, and clique/star marginal preservation. The headline randomized-reduction skeleton remains **NO-GO for assembled claim use** until its previously identified compiler, probability, runtime, and learning bridges are proved.

The bounded claim supported by this increment is:

> Lean verifies that, for a nonempty actual occurrence source, choosing `K = 1 + 157 T J(J-1)` independently tagged copies gives bad ordered-question mass at most `1/T`; if `T >= 4`, the retained good mass is at least `3/4`, is nonzero, and has reciprocal at most `4/3 < 2`.

Do not strengthen this to the manuscript's `tau/100` target, a defined conditioned distribution, uniformity of the conditioned base projection, clique-resampling invariance, an encoded polynomial producer, completion of S3138, actual-star acceptance, randomized hardness, P versus NP, novelty, or publication readiness.
