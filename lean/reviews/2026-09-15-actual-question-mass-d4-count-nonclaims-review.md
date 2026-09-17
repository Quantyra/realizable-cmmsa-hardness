# Actual D=4 ordered bad-question count: non-claims-boundary review

2026-09-15. Read-only review of the frozen actual-source count specialization, its canonical seeded-dependency evidence, and the related manuscript and dependency-ledger wording. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment kernel-checks one construction-specific finite cardinality statement: for an `ActualOccurrenceAllocation.Instance`, the number of ordered row-ID functions that fail `GoodOrderedQuestion I.support` is bounded by `J * (J - 1) * 157 * |I.RowId|^(J - 1)`. The theorem correctly discharges the actual three-uniformity and incidence assumptions of the previously reviewed generic count.

This is still a count, not a probability or retained-mass theorem. It does not prove denominator positivity, normalize the uniform law, construct disjoint-copy padding, justify conditioning or resampling, complete the full actual-source question law, establish source value preservation, prove star acceptance, assemble a randomized reduction, establish hardness, resolve P versus NP, or establish novelty or publication readiness.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `57159656B9F2721BE7ACD180B5F7C3208D4EA9313AA90204DB99ADD662018BCA` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `7A54A9CABA5C1553E018F37D29C41A3FB81741FED251E7CCA0ADAE9E9EF3E622` | Matches the routed freeze. |
| `research/evidence/2026-09-15-actual-question-mass-d4-count-fresh-run/artifact-hashes.txt` | `EF3DA1028341BA32E38D172D5F7D35C62338F20323CC9B16F9D4E283DC59421B` | Matches the routed manifest hash. |

The canonical evidence records unchanged before/after source hashes, main and Checks exit codes `0`, empty stderr, and newly emitted object hashes `BC655AD95C0BB5D283C54865E4F30B314B3CB3861E6E55BAD50DBC2F0318A153` and `0F2FA5AF2886FA6B9CD6A594FFF0D827086FB03BE6678A90A1D0DB059624A902`. The Checks transcript prints the exact specialization signature and only `[propext, Classical.choice, Quot.sound]` for it and the reviewed dependencies.

The forbidden scan records exit `1` because `rg` found no matches; its transcript explicitly reports that no forbidden tokens were found. This is the expected successful no-match status, not a proof failure.

The output root was seeded with 2,794 dependency files from the prior canonical bad-ordered-count target. The current main and Checks objects were excluded from the copy, were absent before compilation, and main then Checks were compiled sequentially. Temporary/probe roots were excluded from `LEAN_PATH`. This is a fresh main-and-Checks build against a recorded precompiled dependency set. It is not a fresh rebuild or independent revalidation of all transitive dependencies, and any evidence summary must retain that qualification.

The compiler emitted only maintenance warnings inherited from or adjacent to this development: deprecated `push_neg`, an unused `simp` argument, the unused `[Fintype X]` section variable on the generic conflict theorem, and a suggestion to use `let` rather than `letI` for the local decidability proof. None changes the frozen specialization or supports a broader claim.

## Exact theorem and assumptions

The terminal transcript confirms:

```lean
theorem actual_bad_ordered_question_count_le
    {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) :
    ((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card ≤
      J * (J - 1) * 157 *
        (Fintype.card I.RowId) ^ (J - 1)
```

The public theorem introduces no assumptions beyond the actual allocation and `J`. It instantiates the generic theorem with:

- row universe `E := I.RowId`;
- coordinate universe `X := I.GlobalVar`;
- rows `row := I.support`;
- incidence bound `D := 4`;
- three-uniformity from `I.support_card`;
- occurrence-sensitive degree from `rowId_incidence_card_le_four I`.

This is the correct instance alignment. The filtered universe counts occurrence row IDs, so equal row values or repeated owners are not silently deduplicated. The local decidability conversion only reconciles proposition-decider representations; it does not add a mathematical hypothesis or alter the counted predicate.

The final `norm_num` step verifies

```text
1 + 3·4 + 9·4² = 157.
```

Thus `157` is the conservative conflict-neighborhood coefficient inherited from the generic proof. It is not a probability, retained fraction, soundness gap, copy count, or tightness claim.

## Fixture audit

The added fixture instantiates the exact actual theorem at `repeatedOwner` and `J = 2`. That allocation has two source rows with repeated ownership while its occurrence IDs remain distinct. The fixture therefore checks the intended occurrence-indexed type alignment and the coefficient's appearance in the compiled theorem.

It does not compute the exact number of bad tuples, show that the bound is sharp, prove a `157`-sized conflict neighborhood, or exercise probability normalization, padding, conditioning, or resampling. The earlier small-`J`, generic mixed-row, direct-conflict, and cross-conflict fixtures retain their limited branch-coverage role.

## Count versus mass boundary

The theorem counts bad elements of the full finite function space `Fin J → I.RowId`, which corresponds combinatorially to ordered independent row choices with replacement. To derive a uniform bad-event probability, a later theorem must relate the total sample-space cardinality to `|I.RowId|^J`, handle the denominator and the possibility that the row universe is empty, and normalize the count bound. Only after those steps can one state the usual ratio resembling `157 * J * (J - 1) / |I.RowId|` under the required positivity assumptions.

Even that probability corollary would not by itself prove the manuscript's retained-law statement. The manuscript at `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`, additionally requires at lines 1148–1158 disjoint-copy padding, preservation of value and degree, a sufficiently small illegitimate-tuple probability, conditioning-loss control, and the clique-resampled marginal statement.

## Ledger and downstream boundary

The planning ledger's pre-freeze wording is appropriately bounded: it identifies this theorem as a construction-specific finite count before probability normalization and retained-mass conditioning, records no new assumptions beyond `I` and `J`, and leaves padding and probability outside the theorem.

At closeout the ledger may record `actual_bad_ordered_question_count_le` as complete with the frozen source hashes, canonical seeded-dependency receipt, and three-lens reviews. It must keep the actual-source bridge conditional until the separate probability, padding, conditioning, and retained-law obligations are proved.

The **direct consumer is a normalized uniform ordered-row probability bound**. The remaining path is:

```text
actual_bad_ordered_question_count_le
  → uniform bad-event probability with row-count positivity
  → disjoint-copy padding and sufficiently small bad mass
  → conditioning-loss and retained-law marginal theorems
  → ordered-to-subset/question-law instantiation
```

## Required public wording

The strongest justified description is:

> Lean verifies that the concrete occurrence allocation has at most `J(J-1)·157·|RowId|^(J-1)` bad ordered row tuples. Probability normalization, padding, conditioning, and the full retained question law remain open.

Do not say that the bad probability is already bounded, good questions have sufficient mass, conditioning is certified, the source bridge is complete, the star construction is accepted, the randomized reduction is formalized, hardness is established, P versus NP is resolved, or the increment is novel or publication-ready.

## Material findings

1. The theorem is correctly specialized to `I.GlobalVar`, `I.RowId`, and `I.support`, preserving occurrence identities.
2. All generic premises are discharged internally using the actual support-cardinality and degree-four theorems; no caller-supplied structural assumption remains.
3. The coefficient `157` is exactly the normalized generic conflict constant and carries no probability or tightness meaning.
4. The fixture checks the actual dependent-type specialization but makes no retained-mass claim.
5. The evidence supports the frozen main and Checks targets with a documented seeded-dependency caveat.
6. Probability normalization, positivity, padding, conditioning, retained-law identity, source completion, reduction, hardness, P-versus-NP, novelty, and publication obligations remain open.

No public-claim promotion follows from this review.
