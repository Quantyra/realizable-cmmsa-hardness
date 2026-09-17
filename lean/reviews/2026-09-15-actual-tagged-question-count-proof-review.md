# Proof-adversarial review: actual tagged-question count

2026-09-15. Top-level read-only review of the frozen `ActualTaggedQuestionMass` increment, its Checks module, and `research/evidence/2026-09-15-actual-tagged-question-count-fresh-run`. No Lean source, commit, push, release, or public claim was changed.

## Verdict

**GO-WITH-NOTES.** The frozen increment correctly specializes the actual occurrence-row conflict upper bound to the arithmetic constant `157`, preserves the occurrence-indexed row carrier through the `Finite3LinSource.ofActual` support conversion, proves the exact tagged-row cardinality `K * I.rows.length`, and obtains the raw bad ordered-question count

```text
J * (J - 1) * 157 * (K * I.rows.length)^(J - 1).
```

The theorem is valid for every natural `J` and `K`, including `0`. The padding constructor is positive for every `J` and `T` because it has a leading `1`. I found no proposition mismatch, decider-dependent filter change, occurrence-identity collapse, bad edge-case arithmetic, axiom leak, or certification blocker.

The notes bound the result to split A. The Checks fixture elaborates `J = 0, 1, 2` at `K = 2`, but does not instantiate `K = 0` or enumerate a sharp bad count. More importantly, this increment stops before rational normalization: positivity of `actualPaddingCopies` alone does not prove a denominator is nonzero, a target bad-mass inequality, retained good mass, or any conditioned-law statement.

## Frozen sources and evidence

| Artifact | SHA-256 | Review result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionMass.lean` | `7BC31AAB2765EB0E0463751DCF2447230D40FC520F2A2D3948DBF40142C139F7` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionMassChecks.lean` | `9A39682BB023B6A47D3FDD5C432B492671CB0AA4DA24A6857AC2BB6C199DF82B` | Matches the routed freeze. |
| `research/evidence/2026-09-15-actual-tagged-question-count-fresh-run/artifact-hashes.txt` | `C3B4B5CE10ABF9EB7046187A4464AEDF05B123D353AAA147945A06406055714D` | Matches the routed manifest hash. |

I independently verified all 33 entries in `artifact-hashes.txt` by byte count and SHA-256. The before/after records contain the same two source hashes. Main and Checks exited `0` with empty stderr and emitted objects with hashes `1741C3CE78523148933F3E186C2604A26E4692DEFBF34D28DF20725DB35D16B2` and `13975746469228B4C2C14A7259F2301681C928EE724217E5127A9CBED5A1A8BB`.

The isolated output root was seeded with 2,802 recorded dependency files while excluding the current main and Checks objects. Both excluded objects were absent before compilation, and main was compiled before Checks. Temporary and probe roots were absent from `LEAN_PATH`. This supports fresh compilation of the two frozen targets against the recorded seeded dependency tree; it is not a clean source rebuild of all transitive dependencies.

The independent source scan found no `sorry`, `admit`, `native_decide`, or source-level `axiom`. Checks profiles all five public declarations. `actualPaddingCopies` has no axioms; the four proved declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The three main-module diagnostics are nonsemantic linter messages about `letI`, `simpa`, and an unused `change`.

## Conflict specialization and conversions

`actual_conflict_degree_le` invokes the previously certified generic `conflict_degree_le` with the actual support family, support size `3`, and incidence bound `D = 4`. Its generic coefficient reduces exactly to

```text
1 + 3 * 4 + 9 * 4^2 = 157.
```

Thus `157` is the exact arithmetic specialization of the generic coefficient and a conservative upper bound on each conflict-neighbourhood cardinality. It is not asserted to be the exact conflict degree of an instance.

The incidence-premise conversion does not change the selected rows. `rowId_incidence_card_le_four I x` and the generic premise both filter `Finset.univ : Finset I.RowId` by the proposition `x ∈ I.support q`; `Finset.filter_congr_decidable` identifies filters elaborated with different decision procedures. This uses proof irrelevance at the implementation boundary without replacing the membership predicate.

The conclusion conversion first proves the function equality

```text
(Finite3LinSource.ofActual I).support = I.support
```

pointwise from `Finite3LinSource.ofActual_support`. Congruence then transports `rowConflict` across that equality for every pair of row IDs. Consequently the result stated over `ofActual I` has the same three conflict branches and the same occurrence-indexed row universe as the generic actual-support result.

## Tagged cardinality and raw count

`actual_tagged_row_card` uses product cardinality, `Fintype.card (Fin K) = K`, and the existing occurrence-row identity

```text
Fintype.card I.RowId = I.rows.length
```

to prove

```text
Fintype.card (Fin K × I.RowId) = K * I.rows.length.
```

The equality counts row identities. Repeated row values or owners are not quotiented or deduplicated.

`actual_tagged_bad_ordered_question_count_le` applies the generic tagged theorem to `Finite3LinSource.ofActual I` with `C = 157`. The filtered event remains literally

```text
¬ GoodOrderedQuestion ((Finite3LinSource.ofActual I).taggedCopy K).support u
```

over `u : Fin J → Fin K × I.RowId`. The final `convert` only identifies the same proposition filters across proof-instance identities and rewrites `Fintype.card I.RowId` as `I.rows.length`. It does not substitute a base bad event or assume uniformity after conditioning.

The universal statement correctly includes all zero-size cases:

- `J = 0`: the unique empty function is good, while the right side is zero.
- `J = 1`: no pair of distinct coordinates exists, so the bad set is empty and `J - 1 = 0` causes no defect.
- `K = 0`, `J > 0`: the function carrier is empty, hence the bad set is empty.
- `J = K = 0`: the empty function exists and is good; the right side is again zero despite the displayed exponent using truncated subtraction.

These cases are inherited from the reviewed generic tagged count and preserved by the specialization. No division or cancellation occurs in this theorem.

## Padding and fixtures

The transparent definition is

```text
actualPaddingCopies J T = 1 + T * (J * (J - 1) * 157).
```

`actualPaddingCopies_pos` proves positivity for every natural `J` and `T`, including zero values, solely from the leading `1`. It does not prove that this copy count meets a normalized-mass target, that the resulting source has positive base row cardinality, or that the construction has a stated output-size or FP bound.

The `smallActual : Instance 1 1` fixture is nonempty at the source parameter. Checks instantiate the raw theorem at `K = 2` for `J = 0`, `1`, and `2`, exercise the tagged row-cardinality rewrite at `K = 2`, and apply positivity as `0 < actualPaddingCopies J 4`. These are useful elaboration and boundary checks. They do not enumerate exact bad-cardinality values, directly instantiate `K = 0`, normalize a probability, or connect `T = 4` to a target inequality.

## Direct normalized-mass consumer

The direct consumer should be an actual-source rational specialization of `tagged_bad_ordered_question_uniform_mass_le`, for example a theorem with explicit hypotheses

```text
0 < K
0 < I.rows.length
```

and conclusion

```text
(badCard : ℚ) /
    (Fintype.card (Fin J → Fin K × I.RowId) : ℚ)
  ≤ (J * (J - 1) * 157 : ℚ) /
      (K * I.rows.length : ℚ),
```

where `badCard` is exactly the filtered cardinality from `actual_tagged_bad_ordered_question_count_le`. A natural declaration name would be `actual_tagged_bad_ordered_question_uniform_mass_le`. Its proof should apply the existing generic rational theorem to `Finite3LinSource.ofActual I`, discharge `C = 157` with `actual_conflict_degree_le`, and rewrite the row cardinality with `rowId_card_eq_rows_length`.

Only after that normalization may a separate theorem connect `actualPaddingCopies J T` to a chosen target and derive strict retained good mass. Conditioning, conditioned base-projection behavior, ordered-to-subset transport, padded-source semantics, producer complexity, star acceptance, reduction assembly, hardness, P versus NP, novelty, and publication readiness remain outside this increment.

## Disposition

Accept the increment as the completed split-A actual tagged raw-count specialization and positive candidate copy-count definition. Record its next direct consumer as `actual_tagged_bad_ordered_question_uniform_mass_le` with explicit positive tag and row-cardinality hypotheses.

**GO-WITH-NOTES.** The notes concern unproved normalization and the limited fixture coverage; they do not identify a defect in the frozen theorem statements or proofs.
