# Actual tagged base-projection transport: non-claims-boundary review

2026-09-15. Top-level read-only review of the frozen `ActualTaggedBaseProjectionTransport` main and Checks modules, their target-fresh certification evidence, and the claim boundary of the resulting base-score transport. No Lean source, certification artifact, commit, push, release, or public claim was changed. This review file is the only artifact written by this lens.

## Verdict

**GO-WITH-NOTES.** The frozen increment proves two correctly separated facts. First, under `0 < K`, averaging a score that depends only on `baseProjection` over the full uniform ordered tagged-tuple space gives exactly the uniform average of that score over ordered base-row tuples. Second, under `4 <= T`, `0 < rowCount`, and pointwise nonnegativity of the base score, its average after restriction to `actualTaggedGoodQuestions` is at most `4/3` times its uniform base-tuple average.

The second theorem is an expectation domination result. It does not say that the conditioned base projection is uniform. The conditioning event depends on tags and row conflicts, so different base tuples can retain different numbers of tag lifts. The proved inequality safely controls that bias by a factor of `4/3`; it does not eliminate the bias or identify the conditioned pushforward with the uniform law.

No unordered-subset transport, clique stationarity, actual-star acceptance, source-hardness instantiation, randomized-reduction assembly, NP-hardness theorem, or conclusion about `P` versus `NP` follows from this increment alone.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Review result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedBaseProjectionTransport.lean` | `A90C2EFB35D40A278F80E873720B8C8181D2CC05F08EBB1A1AED8BBA2584A2E0` | Matches the routed frozen hash and both certification snapshots. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedBaseProjectionTransportChecks.lean` | `795FF7E76726BAB026203245C4FA91272B3D7095D6F1C974F47D7BE7106184B4` | Matches the routed frozen hash and both certification snapshots. |
| `research/evidence/2026-09-15-actual-tagged-base-projection-transport-fresh-run/artifact-hashes.txt` | `5651FFAA82FD899C148AF63228C1478EF176FDBC4DDA97EEAAA78650F4779D71` | Independently recomputed and matches `artifact-hashes-manifest.sha256`. |

The evidence records exit code `0` for main and Checks, stable before/after source hashes, and successful post-run validation. The independently recomputed fresh-object hashes match the receipt: `0C30FA64D1B31F490152AB13A824630B9E877E239578E976EA951409ABE9E379` for main and `1D1FBD1606FB7DEAFA5CED671FB55C02582837BD5653DDA3BDC48D111953BD59` for Checks. The forbidden scan reports no `sorry`, `admit`, `native_decide`, or explicit source-level `axiom`. Both printed theorem profiles contain only `propext`, `Classical.choice`, and `Quot.sound`; no project-specific axiom is reported.

The certification used Lean `4.34.0-rc2` and built the frozen main and Checks into a new target seeded from the prior certified conditioning-transport target, explicitly excluding preexisting objects for these two modules. This is target-fresh main-and-Checks evidence against immutable seeded dependencies. It is not a full source rebuild of every transitive dependency. Main emitted style/linter warnings only; the recorded exit remained `0`.

The canonical manuscript used for comparison is `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`.

## Exact proved boundary

`actualTaggedUniformMean_baseProjection_eq` states, for an actual occurrence-allocation instance, `0 < K`, and any real score `g` on ordered base-row tuples,

```text
actualTaggedUniformMean I K J (g o baseProjection)
  = (sum q, g q) / card(Fin J -> I.RowId).
```

This is exact unconditioned mean equality. Its proof decomposes a tagged tuple into a tag function and a base-row function, sums over the resulting product, uses the exact product cardinality, and cancels the positive tag-space cardinality. It formalizes the equal-fibre fact that every ordered base tuple has the same number of lifts in the full tagged carrier.

`actualTaggedGoodMean_baseProjection_le_four_thirds` states, for `4 <= T`, `0 < rowCount`, and `g >= 0`,

```text
actualTaggedGoodMean I (actualPaddingCopies J T) J (g o baseProjection)
  <= (4/3) * uniformBaseMean(g).
```

It composes the prior certified conditioning inequality with the exact unconditioned base-projection equality. The theorem is valid for arbitrary nonnegative real scores; no upper bound such as `g <= 1` is assumed. For an indicator score it gives the corresponding event-probability upper bound, once that event is represented on this exact ordered base carrier.

The premises have distinct roles. `0 < K` is required by the exact unconditioned cancellation theorem. In the conditioned theorem, `K` is fixed to `actualPaddingCopies J T`, whose positivity follows from its definition; `4 <= T` and `0 < rowCount` are inherited from the retained-mass and conditioning bounds. The conclusions concern semantic finite averages and provide no algorithm or runtime statement.

## Unconditioned equality versus conditioned bias

The strongest exact distributional statement justified here is about the full unconditioned carrier: uniform independent tags have constant fibres over every ordered base-row tuple, so forgetting tags preserves the uniform base-tuple mean.

After restricting to good tagged tuples, constant fibres have not been proved and generally need not hold. A fixed base tuple retains the tag functions that avoid its particular collision/conflict pattern. Different base tuples can induce different conflict graphs and therefore have different numbers of retained tag assignments. Consequently, the pushforward of the uniform good-tagged law may be biased.

The conditioned theorem handles precisely this issue at the score level:

```text
E[g(baseProjection(U)) | U is good] <= (4/3) E[g(Q)],
```

where `U` is uniform on the full ordered tagged carrier and `Q` is uniform on ordered base tuples. Since this holds for every nonnegative `g`, it gives one-sided domination of conditioned base-score expectations by the scaled uniform law. It does not give equality, reverse domination, total-variation control, or uniformity of the conditioned base projection. Claims such as “conditioning preserves the base distribution” or “the retained sampler is uniform on base questions” would be false promotions of the theorem.

## Checks and fixture scope

The Checks module confirms the exact signatures and axiom profiles. Its `J = 0`, `K = 1` fixture checks the exact unconditioned equality. Its two-row, `J = 2`, `T = 4` fixture uses a nonconstant nonnegative score that distinguishes equal and unequal ordered base tuples, then instantiates the conditioned `4/3` inequality. This is a useful nonvacuous elaboration test for score transport.

The fixtures do not compute or compare the conditioned probabilities of all base tuples, establish an unordered quotient law, test a clique-resampling kernel, or instantiate a manuscript failure event. Their role is signature and branch coverage, not reduction-level validation.

## Remaining manuscript and headline obligations

This increment supplies the unconditioned base-score identification requested by the preceding conditioning closeout. The direct next consumer must state the exact ordered-to-subset map used by the manuscript and prove its fibre law on the relevant legitimate carrier. If the manuscript samples unordered `J`-subsets, the proof must establish the required distinctness premise and constant `J!` fibre count or use an accurately weighted alternative. The present ordered-function theorem does not provide that quotient automatically.

The remaining claim-facing path includes:

```text
unconditioned tagged/base mean equality and conditioned score bound  [this increment]
  -> ordered-to-subset transport on the exact legitimate question carrier
  -> concrete clique equivalence and resampling stationarity
  -> actual-star marginal and acceptance theorem
  -> positive-tau parameter choice and completeness union bound
  -> actual-source assumption and value bridge
  -> encoded polynomial-time randomized-reduction assembly
  -> fixed-parameter NP-hardness theorem
  -> learning corollary and manuscript reconciliation
```

The manuscript assertion that every clique-resampled `U'_i` is uniform over legitimate `U` needs a defined finite state space, equivalence classes, kernel, and stationary-measure proof. It is not a consequence of the present one-sided score bound. Likewise, actual-star acceptance needs the joint law of the original question and all resampled blocks plus the relevant constraint-satisfaction event; no such objects appear here.

The actual-source hardness bridge still must connect an encoded bounded-occurrence 3-LIN source theorem to the semantic instance used here, preserve the required value and degree properties under copying, and supply the positive-error parameter choice. The present module assumes an `ActualOccurrenceAllocation.Instance` and proves a finite identity about it; it does not construct that instance from an NP-hard language.

The randomized-reduction obligation still needs an executable encoded map, polynomial size and runtime for all fixed manuscript parameters, completeness and soundness assembly, and a connection to the target decision or promise problem. A semantic finite expectation theorem is one input to that construction, not the construction itself. Therefore no NP-hardness result has been proved by this module, and it supplies no proof that `P = NP` or `P != NP`.

## Permitted claim language

It is accurate to say:

> Lean proves that independent uniform tags preserve the uniform mean of every real score on ordered base-row tuples before conditioning. After restricting to legitimate tagged tuples, every nonnegative base score has mean at most `4/3` times its uniform ordered-base mean, under the certified padding premises.

Keep “before conditioning” attached to the exact equality and “at most `4/3`” attached to the conditioned statement. Do not describe the conditioned base distribution as uniform.

Do not promote this increment to unordered-subset transport, clique-resampling stationarity, actual-star acceptance, completion of the actual-source bridge, source hardness, randomized reduction, NP-hardness, manuscript correctness, novelty, publication readiness, or a resolution of `P` versus `NP`. Those obligations remain open and must be reviewed at their own exact theorem boundaries.
