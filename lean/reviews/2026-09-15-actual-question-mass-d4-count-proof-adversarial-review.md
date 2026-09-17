# Proof-adversarial review: actual question-mass D = 4 count specialization

**Verdict: GO-WITH-NOTES.** The frozen increment proves the exact assumption-free specialization requested for every `ActualOccurrenceAllocation.Instance`: ordered row-ID tuples that fail `GoodOrderedQuestion I.support` have cardinality at most

`J * (J - 1) * 157 * (Fintype.card I.RowId) ^ (J - 1)`.

The proof applies the previously checked generic count with `row := I.support` and `D := 4`, discharges its two premises from the constructed instance itself, and normalizes the conflict constant to `157`. I found no weakening, hidden source promise, row-value quotient, or mismatch between the proposition bounded by the generic theorem and the proposition stated by the specialization. The remaining notes concern probability normalization and later conditioning, which are the direct consumers and are not proved by this count theorem.

## Frozen artifacts and certification

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `57159656B9F2721BE7ACD180B5F7C3208D4EA9313AA90204DB99ADD662018BCA` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `7A54A9CABA5C1553E018F37D29C41A3FB81741FED251E7CCA0ADAE9E9EF3E622` |
| canonical `artifact-hashes.txt` | `EF3DA1028341BA32E38D172D5F7D35C62338F20323CC9B16F9D4E283DC59421B` |

The canonical evidence directory is `research/evidence/2026-09-15-actual-question-mass-d4-count-fresh-run/`. I recomputed the artifact-manifest hash and every hash and byte count listed in that manifest; all entries match. The current main and Checks sources match the frozen hashes above, and `source-before.txt` and `source-after.txt` show those same hashes.

The recorded main and Checks exit codes are both `0`, both stderr files are empty, the main object was built before the Checks object, and neither current bridge object existed in the isolated output target before compilation. The target was seeded from the preceding canonical dependency build while explicitly excluding the current main and Checks objects. The evidence records the Lean `v4.34.0-rc2` executable, `LEAN_PATH`, package revisions and manifests, dependency-seed inventory, commands, output inventory, and object hashes. No temporary or probe root appears in `LEAN_PATH`. This is a fresh build of the changed main and Checks against a pinned seeded dependency tree; it is not represented as a rebuild of every dependency from source.

The forbidden scan found no `sorry`, `admit`, or `native_decide`. The Checks transcript reports only `propext`, `Classical.choice`, and `Quot.sound` for `actual_bad_ordered_question_count_le` and the declarations it consumes. Main's deprecation and linter warnings do not change theorem content.

## Exact theorem and assumption audit

The frozen declaration is:

```lean
theorem actual_bad_ordered_question_count_le
    {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) :
    ((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card ≤
      J * (J - 1) * 157 * (Fintype.card I.RowId) ^ (J - 1)
```

There are no mathematical hypotheses after `I` and `J`. In particular, the theorem does not assume three-uniformity, bounded incidence, distinct source owners, a nonempty row universe, positive sampling mass, or a padding lower bound. `Instance N m` itself contains only `vars : Fin m → Fin 3 → Fin N` and `rhs : Fin m → ZMod 2`; the two generic premises are proved from the construction.

The elaborated signature in `checks.stdout` is propositionally identical to the source declaration. It quantifies over the actual row-ID function space and filters by the same `¬ GoodOrderedQuestion I.support u` predicate. There is no intermediate replacement by equation values, supports modulo equality, source-owner IDs, or a different question predicate.

## Instance alignment

The call

```lean
bad_ordered_question_count_le I.support 4 J I.support_card ...
```

fixes the generic universes exactly as follows:

- `X := I.GlobalVar`;
- `E := I.RowId`;
- `row := I.support`;
- `D := 4`;
- ordered samples remain functions `Fin J → I.RowId`.

The three-coordinate premise is discharged by `I.support_card`, whose conclusion is `(I.support q).card = 3` for every actual `RowId`. That theorem separately covers original and gadget rows and derives cardinality from their injective three-position representations. No row-specific premise is left to the caller.

The degree premise required by the generic theorem is

```lean
∀ x : I.GlobalVar,
  ((Finset.univ : Finset I.RowId).filter
    (fun q => x ∈ I.support q)).card ≤ 4.
```

This is exactly the conclusion of `rowId_incidence_card_le_four I x`. The small `convert` block changes only the selected `DecidablePred` implementation used internally by `Finset.filter`. `Finset.filter_congr_decidable` proves that classical proposition decidability and `Finset.decidableMem` produce the same filtered finset. The element proposition remains literally `x ∈ I.support q`; no semantic hypothesis or transport across a different support relation is introduced.

## Row-ID identity preservation

`I.RowId` is the disjoint sum `Fin m ⊕ I.GadgetId`. Thus original row occurrences and gadget row IDs remain distinct elements even if owners, right-hand sides, row functions, or support finsets happen to agree. Both the sample space `Fin J → I.RowId` and the filtered incidence universe `Finset.univ : Finset I.RowId` count those IDs directly.

The incidence bridge used here previously establishes equality between this row-ID filter cardinality and the occurrence-sensitive degree. Its route uses the complete `rowIndices` enumeration, its `Nodup` proof, and `rows_eq_map`; it does not convert the row list to a finset of row values. Consequently, the present specialization does not silently deduplicate repeated equation values.

The Checks fixture `repeatedOwner : Instance 1 2` makes all six original slots share owner `0`, verifies anchor injectivity, applies the row-ID incidence theorem, and now instantiates `actual_bad_ordered_question_count_le` at `J = 2`. This is a useful identity-regression fixture. Its role is signature and branch coverage; it does not establish sharpness or compute the actual bad-set cardinality.

## Constant normalization and proposition transport

The generic conclusion after the exact instance substitution is

```lean
#bad ≤ J * (J - 1) * (1 + 3 * 4 + 9 * 4 ^ 2) * |I.RowId| ^ (J - 1).
```

Lean proves

```lean
(1 + 3 * 4 + 9 * 4 ^ 2 : Nat) = 157
```

with `norm_num`, and `simpa only` performs that rewrite. Numerically, `1 + 12 + 144 = 157`. The source and target have the same multiplication order and the same natural-number exponent. No inequality relaxation, cast, subtraction rearrangement, or unproved arithmetic side condition occurs in the specialization.

Because the generic theorem already handles `J = 0` and `J = 1`, the specialized theorem does as well: the bad set is empty and the factor `J * (J - 1)` is zero. The theorem is also valid when `I.RowId` is empty because it is a cardinality statement and performs no division. These edge cases become relevant only when converting the result to a probability.

## Direct probability consumer

The next direct consumer should define or reuse the uniform law on `Fin J → I.RowId` and prove the bad-event bound

```text
Pr[¬ GoodOrderedQuestion I.support]
  ≤ 157 * J * (J - 1) / Fintype.card I.RowId
```

for the nondegenerate branch needed by the manuscript. Formally, the numerator is exactly the left side of the accepted theorem and the sample-space cardinality is

```text
Fintype.card (Fin J → I.RowId) = (Fintype.card I.RowId)^J.
```

Cancellation from the accepted numerator bound requires a positive row count and, for the displayed `1/|I.RowId|` form, the appropriate `J ≥ 1` branch. `J = 0` should be handled separately, where the bad probability is zero. Disjoint-copy padding must supply the quantitative lower bound on `Fintype.card I.RowId` needed to make the resulting error `a < 1`. Only after that may one derive positive retained mass, define conditioning on `GoodOrderedQuestion`, and charge the factor `1 / (1 - a)`.

The count theorem itself does not prove any of those divisions, positivity statements, padding properties, conditional-law identities, ordered-to-subset uniformity, marginal preservation, efficient rejection sampler, actual-star acceptance theorem, randomized-reduction assembly, hardness statement, or P-versus-NP conclusion.

## Review disposition

Accept `actual_bad_ordered_question_count_le` as the completed actual-source `D = 4`, `C = 157` cardinality specialization. It exactly consumes `I.support_card` and `rowId_incidence_card_le_four`, preserves row-occurrence identity, and exports the numerator required by the uniform ordered-question probability calculation.

**GO-WITH-NOTES.** The notes are confined to its next dependency: probability normalization needs explicit nonemptiness and edge-case handling, followed by padding and conditioning. They do not expose a defect in the frozen count theorem.
