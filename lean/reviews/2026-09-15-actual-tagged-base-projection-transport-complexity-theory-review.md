# Actual tagged base-projection transport: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for the S3138 source-conditioning bridge  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment proves the correct distributional statement for passing from the full tagged ordered carrier to a score on the original ordered row carrier. It establishes two facts:

```text
E_uniform-tagged[g(baseProjection)] = E_uniform-base[g]

E_uniform-good-tagged[g(baseProjection)]
  <= (4/3) E_uniform-base[g]
```

for every real-valued `g` in the first identity when `K > 0`, and every nonnegative `g` in the second inequality when `T >= 4` and the actual source has at least one row. The first fact is an exact constant-fibre identity. The second combines that identity with the previously certified conditioning inequality. It does not claim that the base projection is uniform after conditioning.

That distinction is mathematically essential. The number of good tagged lifts of a base tuple can depend on its conflict pattern, so the conditioned base pushforward can be biased. The universal nonnegative-score domination proved here is the right response: it is strong enough to control any subsequently defined base failure indicator without requiring equality of the conditioned law to the uniform base law.

This is a valid and useful local bridge into the manuscript completeness argument. The actual failure indicator, ordered-to-subset passage, clique-resampling stationarity, actual-star acceptance, and headline randomized reduction remain unproved. S3138 and the manuscript theorem therefore remain open.

## Frozen artifacts and evidence

| Artifact | Independently observed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedBaseProjectionTransport.lean` | `A90C2EFB35D40A278F80E873720B8C8181D2CC05F08EBB1A1AED8BBA2584A2E0` | Matches the assigned frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedBaseProjectionTransportChecks.lean` | `795FF7E76726BAB026203245C4FA91272B3D7095D6F1C974F47D7BE7106184B4` | Matches the assigned frozen Checks source. |
| `research/evidence/2026-09-15-actual-tagged-base-projection-transport-fresh-run/artifact-hashes.txt` | `5651FFAA82FD899C148AF63228C1478EF176FDBC4DDA97EEAAA78650F4779D71` | Matches the assigned evidence-manifest hash. |
| `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md` | `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240` | Manuscript version assessed, especially its completeness-conditioning passage. |

All 25 manifest entries were independently rehashed and matched their recorded lengths and hashes. The receipt records stable frozen sources, absence of preexisting target objects, and Lean exit codes `0/0` for main and Checks. The generated object hashes are `0C30FA64D1B31F490152AB13A824630B9E877E239578E976EA951409ABE9E379` for main and `1D1FBD1606FB7DEAFA5CED671FB55C02582837BD5653DDA3BDC48D111953BD59` for Checks. This is a target-fresh main-and-Checks compilation against copied, hashed dependency objects. It is not a from-source rebuild of the complete dependency graph.

The forbidden-token scan is clean for `sorry`, `admit`, `native_decide`, and explicit source-level axioms. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the two reviewed theorems.

## Exact mathematical content

`actualTaggedUniformMean_baseProjection_eq` factors the tagged tuple type

```text
Fin J -> (Fin K x I.RowId)
```

into a tag function and a base-row function. Every base tuple has exactly `K^J` lifts. The theorem cancels this common factor in the normalized sum and obtains the exact base uniform mean. Its `0 < K` premise makes the cancellation legitimate. When the equality is read as an equality of probability expectations, the base carrier must also be nonempty; the downstream theorem supplies this through `0 < rowCount`.

`actualTaggedGoodMean_baseProjection_le_four_thirds` instantiates the certified conditioning theorem with `f(u) = g(baseProjection u)` and then rewrites the unconditioned tagged expectation using the exact identity above. Its hypotheses are exactly the required ones:

- `4 <= T`, which supplies retained good mass at least `3/4`;
- `0 < rowCount`, which ensures a nonempty actual source carrier;
- pointwise nonnegativity of `g`.

No independence, Boolean range, or bounded-above condition on `g` is introduced. In particular, a concrete zero-one failure indicator is an immediate admissible instance once it has been defined. Sums of local nonnegative failure indicators are also admissible, which is useful for a union-bound formulation.

The Checks module exposes both exact signatures and their axiom profiles. Its `J = 0` example exercises the normalized identity, and its two-row, `J = 2`, `T = 4` equality-indicator fixture exercises a genuinely nonconstant nonnegative score. The examples do not establish the general theorem, but they are appropriately small branch witnesses alongside the universal proofs.

## Manuscript consumer

The manuscript chooses enough source copies that the illegitimate tagged-tuple mass `a` is at most `1/4`, then states that conditioning can multiply a failure probability by at most `1/(1-a)`. The earlier retained-mass and conditioning modules formalize that denominator and prove the stronger numerical factor `4/3`. This increment now identifies the unconditioned expectation of any score pulled back from base ordered tuples with its exact base uniform expectation.

Consequently, for a concrete base failure indicator `g`, the certified chain has the intended form

```text
Pr[g(baseProjection U) = 1 | U good]
  <= (4/3) Pr[g(Q) = 1],
```

where `U` is uniform on the full tagged ordered carrier and `Q` is uniform on the full base ordered carrier. This is stronger than the manuscript's factor-two allowance for this carrier.

The result corrects a potential misstatement in the prose. It does not justify saying that the conditioned base projection itself is uniform. Instead it justifies the inequality needed for failure control. The manuscript should express the initial conditioned-source step through this domination statement unless a separate exact conditioned pushforward law is later proved.

The next direct theorem should define the actual source failure score and prove its unconditioned base mean bound from the source value. For a `J`-row ordered sample, that likely takes the form of an indicator that at least one selected row is unsatisfied, bounded by `J * epsilon_1`, or a sum of `J` row-failure indicators with the same expectation. The precise statement must use the manuscript's actual assignment and row-sampling semantics.

## Remaining force-bearing gaps

The following dependencies are not supplied by this increment:

1. **Actual failure-score instantiation.** There is no Lean definition connecting `g` to satisfaction of the original bounded-occurrence 3-LIN source, nor a proof that its uniform base expectation is at most `J epsilon_1`.

2. **Ordered-to-subset transport.** The manuscript treats a legitimate query as a set or its resulting incidence/span object. A theorem is still needed for permutation invariance of goodness, the exact `J!` fibre count on injective ordered tuples, and the induced uniform legitimate-subset law. If the actual acceptance theorem remains entirely ordered, the dependency graph should explicitly show why this transport can be omitted; the current manuscript uses set/subspace language, so it cannot presently be assumed away.

3. **Clique-resampling stationarity.** The manuscript claims that each resampled `U'_i` has the required legitimate-query marginal because uniform resampling within an equivalence class preserves it. The reviewed theorems concern only initial conditioning and base projection. They define no equivalence class, transition kernel, transverse-extension count, detailed balance, or stationary law.

4. **Multi-block failure bound.** The factor `(m+1)J` requires a concrete event for the original block and every resampled block, valid marginal bounds for all those blocks, and a finite union bound. Independence is unnecessary for the union bound, but the claimed marginal control is still required for each block.

5. **Tolerance branch.** The current hypotheses give `a <= 1/4`; they do not choose padding from positive `tau` or prove `a <= tau/100`. The final arithmetic and fixed-parameter quantifier order remain open.

6. **Actual-star and headline assembly.** No star acceptance theorem, sampler encoding, polynomial size/runtime theorem, outer reduction composition, soundness assembly, or final randomized-reduction theorem follows from this module.

## Claim boundary

The defensible claim is:

> Lean verifies that the unconditioned uniform tagged ordered tuple has exactly the uniform base ordered tuple as its base-score law, and that after restricting to good tagged tuples every nonnegative base score has expectation at most `4/3` times its uniform base expectation.

Do not strengthen this to exact uniformity of the conditioned base projection, uniformity on legitimate subsets, clique-resampling stationarity, an actual source failure bound, star completeness or soundness, a polynomial-time randomized reduction, the manuscript headline theorem, P versus NP, novelty, or publication readiness.

**GO-WITH-NOTES.** Accept both the exact unconditioned score identity and the conditioned `4/3` domination inequality as the canonical completed base-projection transport obligation. The immediate risk-first consumer is the concrete actual-source failure score and its `J epsilon_1` mean bound, followed by the ordered/subset and clique/star distribution bridges required by the manuscript.
