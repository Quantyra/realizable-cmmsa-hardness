# Actual tagged failure transport: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for the S3138 actual-source completeness bridge  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment establishes the manuscript's one-block completeness failure estimate on the actual padded tagged **ordered-question** carrier. Given an actual occurrence instance with `m > 0` source equations, an assignment `y` satisfying

```text
sourceViolations(y) <= eta * m,
```

and `T >= 4`, it proves

```text
E_uniform-good-tagged[
  1{some one of the J projected source rows is violated by sourceExtension(y)}
]
  <= (4/3) * J * eta.
```

This is the correct conditioned per-block bound needed for the original block `U`. It also has the right numerical strength for the manuscript's eventual conservative union bound: if every one of the `m_star + 1` star blocks has this marginal and `eta = epsilon_1 <= tau / (100 (m_star+1) J)`, then summing the bounds gives `tau/75`. Here `m_star` denotes the manuscript's fixed number of resampled blocks; it is distinct from the Lean parameter named `m`, which is the number of source equations.

The increment does not prove that any clique-resampled block has this marginal, does not form the union over the original and resampled blocks, and does not prove sampler rejection/runtime properties. It therefore closes one force-bearing completeness bridge but not the manuscript completeness argument as a whole.

## Frozen artifacts and evidence

| Artifact | Independently observed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedFailureTransport.lean` | `F3455245210FF8FA22421FD2EE886FB730B3854284F253F4C1082DF0AFFDAC16` | Matches the assigned frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedFailureTransportChecks.lean` | `E712882B84A5DF306EC95CD7212507F9D3B020609679F394AB417997FB448B69` | Matches the assigned frozen Checks source. |
| `research/evidence/2026-09-15-actual-tagged-failure-transport-fresh-run/artifact-hashes.txt` | `4AEDC064895353B3ADF044A15F62F00F91346BBAF752774E9EC167FDCAB3F398` | Matches the finalized manifest payload and its pointer. |
| `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md` | `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240` | Manuscript version compared, especially lines 1137-1175. |

All 25 rows of the finalized evidence manifest were independently rehashed; every recorded length and digest matched. The source hashes were stable, the fresh main and Checks compilation exits are both zero, and the generated object hashes are `C442B43E6F1523EE12CEA6709DA37CDCB48295C175CA6BEE9FA6E3556A1E7F81` and `29AE123326A75ABCD57EF53415417053D11ED3B8D01D3D64C5317B30B51B0265`. This is a target-fresh compilation against copied, hashed dependency objects, rather than a complete rebuild of every dependency from source.

The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and explicit axiom declarations. The seven printed theorem profiles contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact mathematical content

`actualTaggedFailureIndicator` is the zero-one event that at least one position in a tagged ordered `J`-tuple is a bad row for the repeated tagged assignment. `actualTaggedFailureIndicator_eq_baseProjection` proves that this is exactly the corresponding event on the projected base-row tuple. Thus tagging changes neither row satisfaction nor the existential failure event for an assignment repeated across copies.

`actualBaseFailureIndicator_le_sum` is the pointwise union bound

```text
1{exists j, row q(j) is bad} <= sum_j 1{row q(j) is bad}.
```

`sum_eval_eq_card_pow_mul_sum` supplies the exact finite counting identity for one coordinate of a uniformly enumerated function tuple. These combine in `actualBaseFailureIndicator_uniformMean_le` to prove

```text
Pr_uniform-base-tuple[some selected row is bad]
  <= J * violations(x) / |RowId|.
```

No independence premise is needed: this is a finite union bound. Sampling is with replacement on the ordered tuple carrier. The proof handles `J = 0` separately, while positivity of the row carrier follows from the explicit `0 < m` premise.

`actualSourceExtension_failureRate_le` is the exact actual-source assumption bridge. It uses the certified identity

```text
violations(sourceExtension(y)) = sourceViolations(y)
```

and the actual construction's row-count lower bound `m <= |RowId|`. Consequently the source YES premise `sourceViolations(y) <= eta * m`, together with `eta >= 0`, yields

```text
violations(sourceExtension(y)) / |RowId| <= eta.
```

This is mathematically faithful to a source instance with at most an `eta` fraction of its original `m` equations violated. The denominator only grows under the occurrence construction, and the chosen extension satisfies every added equality-cloud row. The theorem assumes the source witness and its error promise; it does not construct that witness or establish the NP-hard source promise.

Finally, `actualTaggedGoodFailureMean_sourceExtension_le` composes the source fraction, the `J`-coordinate union bound, the exact tagged/base projection identity, and the previously certified conditioning domination. The factor `4/3` is the reciprocal cost of retaining at least `3/4` of tagged ordered questions. It is stronger than the manuscript's factor-two allowance. No equality of the conditioned base projection with a uniform law is asserted or needed.

## Match to the manuscript completeness calculation

The manuscript says that an honest global labeling accepts whenever every equation appearing in the original `U` and the `m_star` resampled blocks `U'_i` is satisfied. For the original `U`, the reviewed theorem supplies exactly the required upper bound on the probability that at least one of its `J` projected equations fails, after conditioning the padded tagged tuple to be legitimate.

The final manuscript display

```text
(m_star+1) J epsilon_1 / (1-a) <= tau/75 < tau
```

is consistent with the proved constant. The current retained-mass result gives `1/(1-a) <= 4/3`, and therefore

```text
(m_star+1) * (4/3) * J * epsilon_1
  <= (m_star+1) * (4/3) * J * tau/(100 (m_star+1) J)
  = tau/75,
```

provided the parameter side conditions needed to divide by `J` and `m_star+1` are stated. That last arithmetic and its quantified parameter choice are not proved in this module. Nor does this module prove the stronger padding branch `a <= tau/100`; it uses only `T >= 4`, hence `a <= 1/4` and the `4/3` conditioning factor.

The Checks module exposes the two indicator definitions and all seven theorem signatures, prints axioms for every theorem, and exercises the empty-tuple branch, satisfied and violated row indicators, a nontrivial two-row uniform-mean bound, the source-fraction bridge, and the final conditioned theorem at `J = 0`. The general theorem proves arbitrary `J`; the fixtures are useful interface checks but do not independently exercise a positive-`J` instantiation of the final theorem.

## Remaining force-bearing dependencies

1. **Clique-resampling stationarity.** The manuscript claims each `U'_i` is marginally uniform over legitimate queries because uniform movement inside an equivalence class preserves the measure and every relevant space has the same number of transverse extensions. No equivalence relation, transition kernel, fibre-count theorem, detailed-balance identity, or stationary-law theorem appears here. Until this bridge is proved, the reviewed one-block result cannot simply be copied to the resampled blocks.

2. **Rejection sampler and law realization.** `actualTaggedGoodMean` is the exact mathematical uniform law on the good finite carrier. The module does not implement rejection sampling, prove that its output realizes this law, bound its retries or runtime, or encode the sampler for the eventual reduction. Previously proved retained mass is useful for such a runtime bound but is not itself an executable sampler theorem.

3. **Multi-block rejection/failure union.** The module proves one existential-within-block union bound over `J` coordinates. It does not define the failure events for the original and all `m_star` resampled blocks, show the necessary marginal estimates for each, or apply the outer union bound over `m_star+1` blocks. Independence would not be required for that union bound, but the missing marginal/stationarity facts are required.

4. **Ordered-query to manuscript object transport.** The theorem is on good ordered tagged tuples. If the star construction consumes unordered legitimate subsets, incidence spans, or quotient query objects, permutation invariance and the appropriate constant-fibre/pushforward theorem are still needed. A downstream ordered formulation may avoid this bridge only if the manuscript statement and the complete star kernel are reconciled to that carrier.

5. **Actual-star acceptance.** The honest label assignment, side-condition label transport, clique-consistency constraints, and the implication from satisfaction of all participating equations to acceptance remain to be instantiated on the concrete finite construction.

6. **Outer YES producer and parameter assembly.** The theorem takes `y` and `sourceViolations(y) <= eta*m` as hypotheses. The actual encoded outer reduction must produce the instance and witness promise at the chosen `epsilon_1`, preserve the manuscript's quantifier order, and establish polynomial size/runtime with all fixed constants charged correctly.

7. **Outer soundness and headline reduction.** No parallel-repetition, smooth/advice-game, modified star soundness, HN compilation, sampling/repair composition, encoded randomized reduction, fixed-`L` hardness theorem, learning corollary, or P-versus-NP conclusion follows from this increment.

## `conditional_no_fraction` is not a repeated-game theorem

`ActualOccurrenceSoundness.conditional_no_fraction` must not be reused as though it proved the manuscript's outer repeated-game soundness. Its premise is already a universal source NO promise:

```text
forall y, delta * m <= sourceViolations(y).
```

Its conclusion says that every assignment to the **single regularized occurrence instance** violates at least a fixed scaled fraction of that instance's rows. This is a local value-transfer theorem for the equality-cloud regularizer. It does not construct or analyze repeated questions, advice, shared random vectors, clique resampling, star acceptance, decoding success, or the exponential `2^(-kappa beta J)` bound. Treating it as a repeated-game theorem would skip the principal outer-soundness bridge and would make the headline chain invalid.

## Claim boundary and disposition

The defensible claim is:

> Lean verifies that an actual source assignment violating at most an `eta` fraction of its original equations induces, after occurrence extension, padding, and conditioning on a good ordered tagged `J`-tuple, a probability at most `(4/3) J eta` that at least one selected equation is violated.

Do not strengthen this to a theorem about every clique-resampled block, the `(m_star+1)`-block union, an implemented rejection sampler, uniformity after conditioned base projection, unordered-query stationarity, actual-star completeness, repeated-game soundness, the randomized reduction, the manuscript headline theorem, P versus NP, novelty, or publication readiness.

**GO-WITH-NOTES.** Accept the source-error-to-conditioned-one-block failure theorem as the canonical completed completeness obligation. Keep clique stationarity, sampler-law realization, the outer block union and parameter arithmetic, actual-star acceptance, and all outer-soundness/headline assumptions open in the dependency ledger.
