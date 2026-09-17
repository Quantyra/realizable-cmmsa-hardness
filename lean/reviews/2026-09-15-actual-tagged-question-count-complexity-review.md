# Actual tagged-question count: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for source-preserving tagged-copy padding (S3138)  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment correctly completes the actual-source raw-count specialization. It proves that every actual occurrence row has at most `157` conflicting occurrence rows, that the tagged row carrier has exactly `K * I.rows.length` elements, and that

```text
# bad ordered tagged J-tuples
  <= J(J-1) * 157 * (K * I.rows.length)^(J-1).
```

It also defines the positive arithmetic candidate

```text
actualPaddingCopies J T = 1 + T * (J(J-1) * 157).
```

These are mathematically relevant inputs to the manuscript's discarded-illegitimate-tuple step. They do not yet prove a normalized bad mass, a target retained-mass inequality, a polynomial-time encoded producer, a conditioned law, star acceptance, hardness, or any headline conclusion. Source-preserving tagged-copy padding (S3138) therefore remains active.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionMass.lean` | `7BC31AAB2765EB0E0463751DCF2447230D40FC520F2A2D3948DBF40142C139F7` | Matches the routed frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionMassChecks.lean` | `9A39682BB023B6A47D3FDD5C432B492671CB0AA4DA24A6857AC2BB6C199DF82B` | Matches the routed frozen Checks source. |
| `research/evidence/2026-09-15-actual-tagged-question-count-fresh-run/artifact-hashes.txt` | `C3B4B5CE10ABF9EB7046187A4464AEDF05B123D353AAA147945A06406055714D` | Matches the routed evidence-manifest hash. |

I independently rehashed all 33 entries in `artifact-hashes.txt`; every recorded byte count and SHA-256 matched. The evidence records unchanged before/after source hashes, main and Checks exit codes `0`, empty stderr, and fresh target objects with SHA-256 values `1741C3CE78523148933F3E186C2604A26E4692DEFBF34D28DF20725DB35D16B2` and `13975746469228B4C2C14A7259F2301681C928EE724217E5127A9CBED5A1A8BB`.

The target output directory was seeded with recorded dependency objects while excluding the two reviewed target objects, then compiled main before Checks. This certifies fresh compilation of the frozen targets against the disclosed precompiled dependency set; it is not a from-source rebuild of every transitive dependency. The forbidden scan is empty. `actualPaddingCopies` uses no axioms, and the proved declarations use only the standard inherited `propext`, `Classical.choice`, and `Quot.sound`. The main output contains three nonsemantic linter warnings.

## Actual constant `C = 157`

`actual_conflict_degree_le` supplies the generic tagged counting theorem with an internally discharged conflict-fibre bound. The actual occurrence allocation provides three-element row supports and incidence at most four. The generic conservative coefficient specializes to

```text
1 + 3*4 + 9*4^2 = 157.
```

Thus `157` is the exact numerical specialization of the proved generic coefficient and an upper bound on each actual conflict neighbourhood. It is not an assertion that every neighbourhood has exactly `157` members, nor is it itself a bad-question count or probability.

The support conversion from `Finite3LinSource.ofActual I` back to `I.support` preserves the occurrence-indexed row identities. Repeated source owners are not deduplicated. This is the correct carrier for uniform sampling of semantic equation occurrences after regularization.

## Raw count and row count

`actual_tagged_bad_ordered_question_count_le` is a one-sided cardinality bound on the full ordered function space

```text
Fin J -> Fin K x I.RowId.
```

It counts bad tuples under the support of `(Finite3LinSource.ofActual I).taggedCopy K`. It does not divide by the total number `(K * I.rows.length)^J` and therefore is not a normalized-mass theorem.

`actual_tagged_row_card` proves the exact identity

```text
Fintype.card (Fin K x I.RowId) = K * I.rows.length.
```

Here `I.rows.length` is the semantic occurrence-row count, not the raw variable parameter `N` and not simply the raw source-equation parameter `m`. Existing upstream theorems identify

```text
I.rows.length = m + 4 * I.edgeCount,
m <= I.rows.length,
I.rows.length <= (1 + 18 * FixedPortCycleFamily.degree) * m.
```

Consequently the natural manuscript denominator after tagging is

```text
N_outer = K * I.rows.length,
```

provided a later theorem or interface explicitly makes that identification. The current module contains no `N_outer` declaration and no encoded-size bridge.

## Zero cases

The count statement is valid for all natural `J` and `K`.

- If `J = 0`, the unique empty tuple is good and the bad count is zero.
- If `J = 1`, there is no distinct-position witness and the bad count is zero.
- If `K = 0` and `J > 0`, the function carrier is empty and the bad count is zero.
- If `J = K = 0`, the unique empty tuple is again good.

These cases make the raw theorem total; they do not create a normalized law. For `K = 0` and `J > 0`, the total carrier has cardinality zero. For `J = 0`, the total function space has one point even when the tagged row carrier is empty, but that degenerate empty-question law is not the manuscript's positive-row sampling regime.

`actualPaddingCopies J T` is never zero, including at `J = 0`, `J = 1`, and `T = 0`, because of its leading `1`. This proves tag-count positivity only. If `I.rows.length = 0`, the tagged row universe is still empty for every positive copy count. A route-facing normalized theorem therefore needs positive base rows, naturally obtained from the existing hypothesis `0 < m` via `I.rows_length_pos`.

## Padding inequality and parameter complexity

Let

```text
A = 157 * J(J-1),
K = actualPaddingCopies J T = 1 + T*A,
M = I.rows.length.
```

The already certified generic normalized theorem suggests the following mathematical consequence when `0 < T` and `0 < M`:

```text
Pr[bad] <= A/(K*M) < 1/T.
```

Indeed `K > T*A` and `M >= 1`. This strict target inequality is not stated or proved in the frozen increment. At `T = 0`, `K = 1`, but `1/T` has no meaningful target interpretation.

The manuscript fixes `m, xi, h, J, beta`, and then a positive constant completeness error `tau`, before the source input length varies. Under that constant-parameter order, one may choose a fixed positive integer

```text
T >= max(ceil(100/tau), 4),
```

so the inferred bound is below `min(tau/100, 1/4)`. Then `J`, `T`, and `K` are constants independent of source input length, and materializing `K` tagged copies can in principle preserve polynomial time and linear-size blowup, assuming the missing encoded producer and its correctness proof are supplied.

The arithmetic definition alone does not establish that producer. If `T` is instead treated as an unrestricted binary input, explicitly outputting `K = 1 + 157T J(J-1)` copies takes time proportional to the numeric value of `K`, which can be exponential in the bit length of `T`. Accordingly, the justified complexity interpretation is fixed-parameter or a regime where the numeric copy count is polynomially bounded in the original encoded input size. No uniform polynomial-time claim in binary `J,T` follows from this module.

## Manuscript relevance

The submission manuscript's discarded-tuple paragraph says to take enough disjoint copies that the illegitimate probability `a` is at most `min(tau/100, 1/4)`, uses an `O(J^2/N_outer)` bound, asserts preservation of value and degree, and then conditions on legitimate tuples. This increment supplies the actual constant and raw-cardinality side of that paragraph:

```text
C = 157,
N_outer candidate = K * I.rows.length,
#bad <= 157 J(J-1) * N_outer^(J-1).
```

After a positive-denominator normalization, this yields the intended explicit form

```text
Pr[bad] <= 157 J(J-1) / N_outer.
```

The manuscript relevance is direct and force-bearing because the tag factor grows the denominator while leaving the conflict-fibre bound at `157`. The present declarations stop before the manuscript can consume that force: they do not state the probability ratio, connect `T` to `tau`, establish positive retained mass, combine tagged cardinality with the already proved semantic value preservation, or implement the padded instance.

The later manuscript sentence that uniform clique resampling preserves the legitimate-tuple measure is also independent. Conditioning on tagged goodness generally biases the base-row projection, so no conditioned base-uniformity or star-law transport may be inferred from the unconditioned raw count.

## Direct consumer and accepted claims

The immediate direct consumer should be a theorem such as

```text
actual_tagged_bad_ordered_question_uniform_mass_le
```

with explicit hypotheses `0 < K` and `0 < I.rows.length`, applying the existing generic rational mass theorem at `C = 157` and rewriting `Fintype.card I.RowId` to `I.rows.length`. The next consumer should specialize `K` to `actualPaddingCopies J T`, assume `0 < T` and positive source rows, prove the strict `< 1/T` bound, choose `T` from the fixed manuscript tolerance, and derive strictly positive good mass. The encoded tagged-copy producer and output/runtime proof remain a separate algorithmic consumer.

The strongest justified claims from this increment are:

- actual occurrence-row conflict neighbourhoods have cardinality at most `157`;
- the tagged row universe has exact cardinality `K * I.rows.length`;
- the displayed one-sided raw bad-tuple count holds for all natural `J,K`;
- `actualPaddingCopies J T` is positive for all natural `J,T`;
- under the manuscript's fixed-parameter reading, this constructor is a plausible constant-copy choice for the next normalized theorem and producer.

No normalized mass, polynomial-time producer, conditioned law, conditioned projection, clique-resampling invariant, star acceptance theorem, randomized reduction, hardness theorem, P-versus-NP result, manuscript headline, novelty claim, or publication-readiness conclusion follows yet.

## Verdict

**GO-WITH-NOTES.** The actual `C = 157` specialization, raw count, exact occurrence-row count, and padding positivity are correct and directly relevant to the manuscript's retained-question denominator. The notes are live consumer obligations: positive-row normalization, the explicit padding-to-tolerance inequality, fixed-parameter instantiation, encoded producer and size/runtime proof, retained-mass positivity, and every subsequent conditioning, star, and hardness bridge. This increment should be accepted as split-A counting progress, not as closure of S3138 or of the manuscript route.
