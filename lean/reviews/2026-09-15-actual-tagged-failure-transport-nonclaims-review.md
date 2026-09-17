# Actual tagged failure transport: non-claims-boundary review

2026-09-15. Top-level read-only review of the frozen `ActualTaggedFailureTransport` main and Checks modules, their target-fresh certification evidence, and the manuscript claim boundary. No Lean source, certification artifact, commit, push, release, or public claim was changed. This review file is the only artifact written by this lens.

## Verdict

**GO-WITH-NOTES.** The frozen increment proves a concrete one-block completeness estimate on the actual semantic occurrence-allocation source. If an original assignment violates at most `eta * m` source rows, with `eta >= 0`, `m > 0`, and `T >= 4`, then the good-set average of the indicator that at least one of the `J` ordered tagged queries is violated by the repeated source-extension assignment is at most

```text
(4/3) * J * eta.
```

This composes an exact tagged-to-base failure-indicator identity, a union bound over the `J` ordered coordinates, an exact finite averaging calculation, the source-extension violation identity, and the previously certified `4/3` conditioning transport. It does not prove clique or star resampling stationarity, a multi-block union bound, honest star acceptance, a source hardness theorem, a randomized reduction, NP-hardness, publication readiness, or a conclusion about `P` versus `NP`.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Review result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedFailureTransport.lean` | `F3455245210FF8FA22421FD2EE886FB730B3854284F253F4C1082DF0AFFDAC16` | Matches the frozen source hash and both certification snapshots. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedFailureTransportChecks.lean` | `E712882B84A5DF306EC95CD7212507F9D3B020609679F394AB417997FB448B69` | Matches the frozen source hash and both certification snapshots. |
| `research/evidence/2026-09-15-actual-tagged-failure-transport-fresh-run/artifact-hashes.txt` | `4AEDC064895353B3ADF044A15F62F00F91346BBAF752774E9EC167FDCAB3F398` | Independently recomputed, matches the manifest pointer, and all 25 listed artifact rows match current bytes. |

The initially routed evidence hash `FFE4DDE92ECEC9A0F0F42773FC336062F7D38C27EBECDCDD031CA61A57B32862` was sampled while the certifier was still finalizing the receipt. The finalized authoritative artifact-list hash and pointer content are `4AED...F398`; the pointer file itself hashes to `FDCEB5DC572695991954829BB0D3B4397E17F3BF80B39066908B063433C38C65`. This was an orchestration timing race, not a source or build discrepancy.

The evidence records exit code `0` for main and Checks, unchanged before/after source hashes, and successful post-run validation. The independently recorded fresh-object hashes are `C442B43E6F1523EE12CEA6709DA37CDCB48295C175CA6BEE9FA6E3556A1E7F81` for main and `29AE123326A75ABCD57EF53415417053D11ED3B8D01D3D64C5317B30B51B0265` for Checks. The forbidden scan found no `sorry`, `admit`, `native_decide`, or explicit source-level `axiom`. Every printed theorem profile lists only `propext`, `Classical.choice`, and `Quot.sound`; no project-specific axiom appears.

The certification used Lean `4.34.0-rc2` and compiled the two frozen modules into a new target seeded from the prior certified base-projection-transport target while excluding preexisting objects for these two modules. This is target-fresh main-and-Checks evidence against a recorded immutable dependency seed. It is not a full source rebuild of all transitive dependencies. The main and Checks logs contain style/linter warnings only, with successful exits.

The manuscript compared in this review is `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`.

## Exact proved claim

`actualTaggedFailureIndicator I x u` is a real-valued `0`/`1` indicator for the event that some coordinate of the ordered tagged tuple

```text
u : Fin J -> Fin K x I.RowId
```

is a bad row of the tagged-copy source under `repeatAssignment x`. `actualBaseFailureIndicator I x q` is the corresponding indicator on an ordered base-row tuple. The theorem `actualTaggedFailureIndicator_eq_baseProjection` proves that the tagged event is exactly the base event after forgetting tags. This uses the existing tagged-copy bad-row and repeated-assignment restriction identities; it is not a probabilistic approximation.

`actualBaseFailureIndicator_le_sum` gives the pointwise union bound: the indicator that any queried base row fails is at most the sum of the `J` individual row-failure indicators. `sum_eval_eq_card_pow_mul_sum` then supplies the exact constant-fibre count for evaluation at one coordinate of the full ordered function space. Together they prove

```text
uniformBaseMean(any of J queried rows fails)
  <= J * violations(x) / card(I.RowId).
```

This is an expectation bound on ordered tuples sampled with replacement. It neither requires nor proves that the base coordinates are distinct.

`actualSourceExtension_failureRate_le` specializes the row-failure rate to an assignment `I.sourceExtension y`. From

```text
I.sourceViolations y <= eta * m
```

it derives

```text
violations(I.sourceExtension y) / card(I.RowId) <= eta.
```

The proof uses the exact existing source-extension violation identity and the fact that the occurrence-allocation row universe contains at least the `m` original source rows. The premise `eta >= 0` is needed when enlarging the denominator reference from `m` to the actual row count. The theorem does not produce `y`, prove the premise `hy`, or connect `hy` to an encoded NP-hard promise.

Finally, `actualTaggedGoodFailureMean_sourceExtension_le` sets the tag count to `actualPaddingCopies J T` and applies the certified conditioned base-score inequality. Its exact hypotheses and conclusion are:

```text
4 <= T
0 < m
0 <= eta
I.sourceViolations y <= eta * m
------------------------------------------------------------
actualTaggedGoodMean I (actualPaddingCopies J T) J
  (actualTaggedFailureIndicator I (I.sourceExtension y))
    <= (4/3) * J * eta.
```

Thus the justified reading is a conditioned one-block failure-mean upper bound over the finite set `actualTaggedGoodQuestions`. The result concerns the semantic source and a particular repeated source-extension assignment. It is not an algorithm, a sampling-runtime result, or an encoded reduction theorem.

## Manuscript relationship

The theorem provides a concrete form of part of the completeness accounting around manuscript lines 1148--1164. It justifies the factor-`4/3` conditioned bound for the original ordered tagged question block when the source assignment has normalized violation rate at most `eta`. Taking `eta = epsilon_1` would yield the one-block estimate `(4/3) J epsilon_1`, after a later theorem supplies the required source assignment and the exact premise on `sourceViolations`.

It does not establish the manuscript's full `(m+1)J epsilon_1/(1-a)` bound. In particular, the theorem contains one original ordered tagged block and no family of `m` clique-resampled blocks. A later result must define the joint star experiment, prove the required marginal law for every resampled block, transfer this failure estimate to each marginal, and perform the union bound over the original block plus all resampled blocks.

The theorem also does not prove the manuscript's claim that clique resampling preserves the uniform legitimate-question measure. Its imports contain conditioning and base-projection transport, but the current source has no clique equivalence relation, resampling kernel, transverse-extension count, stationarity statement, or star distribution. Those are independent obligations and cannot be inferred from the one-block average.

## Claim boundaries that remain open

The following promotions are unsupported by this increment:

- **Clique/star stationarity:** no resampling relation, kernel, or stationary marginal is defined or proved.
- **Multi-block union:** the theorem controls one `J`-coordinate block; it does not quantify over `m+1` blocks or their joint law.
- **Honest star acceptance:** failure of queried source equations is only one condition in the intended composed acceptance proof. The actual labeling, consistency constraints, star predicate, and acceptance implication remain absent.
- **Source hardness:** `hy` is an assumption about a supplied assignment. No NP-hard source language, YES-instance producer, NO gap, encoded occurrence-allocation construction, or value-preservation theorem is established here.
- **Reduction:** there is no encoded polynomial-time randomized map, output-size proof, parameter assembly, completeness/soundness theorem, or target decision/promise problem theorem.
- **Headline consequences:** no NP-hardness, learning corollary, manuscript-wide correctness, novelty, publication readiness, `P = NP`, or `P != NP` statement follows.

The numerical conclusion is also not the manuscript's final `tau` inequality. The module has no `tau`, does not choose `epsilon_1 <= tau/(100(m+1)J)`, and does not show the final arithmetic `<= tau/75 < tau`. Those parameter and assembly steps remain separate.

## Checks and fixtures

The Checks module verifies the declarations and prints the axiom profiles for all seven theorems. Its fixtures cover an empty ordered tuple with zero failure, a satisfied one-row query, a failing query in a two-row occurrence-allocation instance, the `J = 0` headline specialization, the nontrivial `J = 1` uniform-mean inequality, and a source-extension failure-rate instantiation.

These are useful elaboration and branch checks. They do not instantiate the headline theorem at a positive `J` with a proved source-error premise, enumerate the conditioned good set, test a clique-resampling marginal, or validate a star/reduction-level construction. The general theorem's frozen signature and kernel-checked proof, rather than the fixtures, carry the mathematical claim.

## Permitted claim language

It is accurate to say:

> Lean proves that, for the actual semantic occurrence-allocation source, an assignment violating at most an `eta` fraction relative to the original `m` source rows induces a good ordered tagged-question block failure mean at most `(4/3) J eta`, under `eta >= 0`, `m > 0`, and `T >= 4`.

Keep “ordered tagged-question block,” “good-set mean,” the source-extension assignment, and the explicit premises attached to the statement. Do not describe this as uniformity after conditioning, clique/star stationarity, the full completeness union bound, honest star acceptance, source hardness, a randomized reduction, NP-hardness, publication readiness, or a resolution of `P` versus `NP`.

## Remaining dependency path

```text
actual-source one-block conditioned failure mean  [this increment]
  -> concrete clique equivalence and resampling stationarity
  -> transfer of the one-block estimate to every star marginal
  -> honest-labeling acceptance implication
  -> multi-block union and positive-tau parameter arithmetic
  -> encoded source-hardness and value bridge
  -> polynomial-time randomized-reduction assembly
  -> fixed-parameter NP-hardness theorem
  -> learning corollary and manuscript reconciliation
```

The reviewed result is a substantive completeness bridge, but its safe consumer is the next exact distributional theorem. Closing the broader manuscript or headline claim at this point would exceed the evidence.
