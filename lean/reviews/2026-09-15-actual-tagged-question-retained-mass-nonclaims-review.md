# Actual tagged-question retained mass: non-claims-boundary review

2026-09-15. Read-only review of the frozen `ActualTaggedQuestionRetainedMass` main and Checks modules and the certified fresh-run evidence. No Lean source, compilation, commit, push, release, public wording, or evidence artifact was changed. This review file is the only artifact written by this lens.

## Verdict

**GO-WITH-NOTES.** The frozen increment proves exact finite-cardinality definitions and identities for good and bad ordered tagged-question mass. For the explicit tag count

```text
actualPaddingCopies J T = 1 + T * (J * (J - 1) * 157),
```

it proves, assuming `0 < T` and `0 < m`, that the bad full-space uniform mass is at most `1/T`. Under `4 <= T` and `0 < m`, it proves good mass at least `3/4`, positive good cardinality, reciprocal good mass at most `4/3`, and reciprocal good mass strictly below `2`.

These are normalized counting and reciprocal-factor facts for the explicitly defined full finite space `Fin J -> Fin K × I.RowId`. They do not define a conditional distribution, prove a conditional-probability inequality, establish uniformity of the base-row projection after conditioning, transport an encoded source-output distribution, discharge the manuscript target involving `tau/100`, complete the headline reduction, or imply any P-versus-NP conclusion.

## Frozen artifacts and evidence integrity

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionRetainedMass.lean` | `22F98B1FF1F84D0BED94744A62873A933C7B531EA310DA953D01B5FBA1581E91` | Matches the routed freeze and both evidence source snapshots. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionRetainedMassChecks.lean` | `9289DD63BEC7798158DF36D7E71D2C0E9365EB34401955C45B6FDF4C7177A2DB` | Matches the routed freeze and both evidence source snapshots. |
| `research/evidence/2026-09-15-actual-tagged-question-retained-mass-fresh-run/artifact-hashes.txt` | `3D62FA741B1CC5AE6B8704D52444621059F06063B6812889FF2765D9A2C4E5D1` | Matches the certified manifest pointer. Every listed size and SHA-256 matches the current evidence bytes. |

`artifact-hashes-manifest.sha256` contains the certified `3D62...E5D1` hash of `artifact-hashes.txt`; the SHA-256 of the pointer file itself is a different value and is not the routed manifest claim. This distinction is represented correctly in the evidence.

The evidence records stable before/after source hashes, main and Checks exit codes `0`, and newly emitted object hashes `4BF0B86EA74363B9F58CDB97E27D4863402D1913B209E10B30B7CCBF8AFB6AB6` and `85B12CFC079580878EEBE701705B4E573A0A89B5D9E09A2FF09457A7EA31864B`. The forbidden scan is clean. An independent read-only scan of the two frozen source files also found no `sorry`, `admit`, `native_decide`, or source-level `axiom` declaration. The recorded axiom report lists only `[propext, Classical.choice, Quot.sound]` for the reviewed declarations and no project-specific axiom.

The build evidence is appropriately scoped. It directly compiled the frozen main and Checks modules into an isolated target after seeding recorded dependencies from a prior certified target while excluding the two current target artifacts. It is fresh evidence for these two modules against that recorded dependency set, not an independent source rebuild of all transitive dependencies. The only main-log findings are two unused-`simp` linter warnings, which do not expand or weaken the theorem statements.

## Exact normalized-mass boundary

`actualTaggedGoodQuestions I K J` and `actualTaggedBadQuestions I K J` filter the full function space

```text
Fin J -> Fin K × I.RowId
```

by `GoodOrderedQuestion` and its negation. `GoodOrderedQuestion` requires both injectivity of the ordered tuple and the existing finite support-set geometry predicate. The corresponding masses are rational cardinality ratios with the cardinality of that same full function space as denominator.

The module proves the following exact or one-sided statements:

- good-cardinality plus bad-cardinality equals total cardinality;
- when `K > 0` and `m > 0`, the total cardinality is positive and good mass equals `1 - bad mass`;
- under the same positivity premises, bad mass is at most `157 J(J-1) / (K * I.rows.length)`;
- for `K = actualPaddingCopies J T`, `T > 0`, and `m > 0`, bad mass is at most `1/T`;
- if additionally `T >= 4`, good mass is at least `3/4`, the good set is nonempty, and the reciprocal good mass is at most `4/3` and strictly below `2`.

“Uniform mass” is justified here only as shorthand for this finite full-space cardinality ratio. No probability-measure, sampler, random-variable, rejection process, or conditional-law object occurs in the reviewed statements.

The premise `0 < m` is used to derive that the actual row universe is nonempty. It is not a source promise, satisfiability promise, hardness hypothesis, or distributional premise. The padding parameter `K` is a type-level tag count for the semantic `taggedCopy`; this module does not establish an encoded producer or a runtime/output-size bound for materializing it.

## Conditioning boundary

The declarations named `actual_tagged_conditioning_factor_le_four_thirds` and `actual_tagged_conditioning_factor_lt_two` prove inequalities about the rational expression

```text
1 / actualTaggedGoodMass I (actualPaddingCopies J T) J.
```

That expression is the numerical normalization factor one would use when conditioning the full-space uniform law on the good event. The names do not themselves construct that conditioned law. In particular, the module does not prove a statement of the form

```text
Pr[failure | good] <= Pr[failure] / Pr[good],
```

does not identify which failure event is being conditioned, and does not prove a rejection sampler efficient or distributionally correct.

The theorem also does not prove that the base projection `u |-> fun i => (u i).2` stays uniform after restricting to good tagged tuples. Goodness depends jointly on repeated tags and conflicts among the selected base rows, so the number of admissible tag assignments can vary with the base tuple. The prior exact unconditioned fibre count does not survive conditioning without a separate equal-fibre, weighting, or transport theorem.

Accordingly, “conditioning costs a factor at most `4/3`” is acceptable only when explicitly described as the certified reciprocal retained-mass bound. It must not be presented as a proved conditioned failure bound, uniform conditioned marginal, or completed sampler statement.

## `tau/100` boundary

The reviewed module contains no parameter `tau`, no representation of the manuscript's real or rational tolerance, and no theorem comparing `1/T` with `tau/100`. It proves the parametric estimate `bad mass <= 1/T` and the concrete quarter-mass consequence for `T >= 4`.

To reach the manuscript target

```text
a <= min(tau/100, 1/4),
```

a later theorem must state the type and positivity/range assumptions for `tau`, choose or assume an integer `T` satisfying the exact cross-type inequality `1/T <= tau/100` as well as `4 <= T`, and connect `a` to the certified bad mass. The current arithmetic makes such a step plausible but does not discharge it. It is therefore inaccurate to say that this increment proves the `tau/100` target or the full discarded-tuple tolerance.

## Source-output and headline-reduction boundary

The semantic tagged-copy dependency defines copied rows and variables and separately proves per-copy violation decomposition. This retained-mass increment does not prove that an encoded source producer outputs that semantic object, that the output law is the full-space uniform tuple law used in these ratios, or that any subsequent map preserves the required distribution.

The following remain outside the reviewed theorem boundary:

- an encoded, polynomial-time, polynomial-output-size construction for the chosen number of tagged copies;
- transport of actual source YES/NO promises, optimum value, or violation fractions through the full encoded producer path;
- a conditional sampler and its base-row or legitimate-question pushforward law;
- ordered-tuple to unordered-question equal-fibre transport;
- clique resampling, uniform clique marginals, star acceptance, or repetition soundness;
- assembly and parameter bookkeeping for the claimed randomized reduction;
- the fixed-parameter hardness headline, the learning corollary, manuscript correctness, novelty, or publication readiness;
- `P = NP`, `P != NP`, or any other resolution of P versus NP.

The fact that the module imports earlier semantic bridges does not turn their separate conclusions into a source-output distribution theorem. Each transport step still requires an explicit composed statement with its hypotheses discharged.

## Checks boundary

The Checks module confirms the declaration signatures and axiom profiles. Its fixtures establish `actualPaddingCopies 0 4 = 1`, `actualPaddingCopies 1 4 = 1`, and `actualPaddingCopies 2 4 = 1257`; instantiate the quarter bad-mass theorem at `J = 0` and `J = 1`; and instantiate positive good cardinality at `J = 2` for a one-row actual instance.

These fixtures test elaboration and small parameter instances. They do not compute exact good or bad mass for the `J = 2` case, show sharpness, exercise `tau/100`, define a conditional law, test conditioned base uniformity, or verify a source-output distribution or reduction.

## Required wording

The strongest justified concise description is:

> For the actual semantic 3-LIN source with a nonempty original row set, Lean defines good and bad mass as rational cardinality ratios over the full ordered tagged-tuple space. With `K = 1 + T * 157 J(J-1)`, it proves bad mass at most `1/T`; for `T >= 4`, good mass is at least `3/4`, the good set is nonempty, and the reciprocal retained mass is at most `4/3` and below `2`.

If conditioning is mentioned, add:

> The reciprocal bound is numerical input for a later conditioning argument; no conditional law, conditioned base uniformity, or conditioned failure-event theorem is proved here.

Do not say that the increment establishes the `tau/100` tolerance, uniformity after conditioning, source-output distribution transport, the headline reduction, a hardness theorem beyond already separately reviewed statements, or any P-versus-NP conclusion.

## Material findings

1. The frozen source and certified evidence hashes are internally consistent; every artifact row in the evidence hash list verifies against current bytes.
2. The exact normalized quantities are finite cardinality ratios over the full ordered tagged-tuple space, with denominator positivity discharged from `K > 0` and `m > 0`.
3. The new substantive force is `bad mass <= 1/T`, hence good mass at least `3/4` and positive for `T >= 4`, plus the reciprocal retained-mass bounds.
4. The declarations named as conditioning factors are arithmetic reciprocal bounds, not a formal conditional distribution or conditioned-event theorem.
5. The `tau/100` target, conditioned base uniformity, source-output law transport, and all headline-reduction assembly remain open.
6. No public-claim promotion and no P-versus-NP claim follows from this increment or this review.

