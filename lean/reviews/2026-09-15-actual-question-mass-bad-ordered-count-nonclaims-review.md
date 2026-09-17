# Bad ordered-question count: non-claims-boundary review

2026-09-15. Read-only review of the frozen bad-ordered-count increment, its canonical seeded-dependency evidence, and the related manuscript and dependency-ledger wording. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment kernel-checks a generic cardinality bound for bad ordered row tuples under explicit three-uniformity and incidence assumptions. It counts functions `u : Fin J → E` that fail the declared `GoodOrderedQuestion` predicate. This is the combinatorial numerator needed for a later uniform-law probability estimate.

The theorem does not define a probability distribution, divide by the total number of tuples, prove retained mass or positivity, construct disjoint-copy padding, justify conditioning or resampling, instantiate the actual occurrence source at `D = 4`, close the source bridge, prove star acceptance, assemble a randomized reduction, establish hardness, resolve P versus NP, or establish novelty or publication readiness.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `E87EE1F98ED5D431B288EB88AD278BE05D398461FAE4218A74A0CEDDBC792FC3` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `E4A8CB6663501D7012E967D8B436366536B2AD0D49C6156C0A75882CBE52C36A` | Matches the routed freeze. |
| `research/evidence/2026-09-15-actual-question-mass-bad-ordered-count-fresh-run/artifact-hashes.txt` | `EB9B26EB3262E97D55B4E4E3BECAF0F01FF5EC46913E9B7152CA2F304C34C8FF` | Matches the routed manifest hash. |

The canonical evidence records unchanged source hashes, final main and Checks exit codes `0`, empty stderr, and newly emitted object hashes `D6FA76482E683528EEC2AF2F62B6F4E9CB7290CDA553669C6131BE36A09D460D` and `2676252E1CF77B93CB14B75088546A1EC3A930AD74552E02D9754C757B21282C`. The Checks transcript prints the expected theorem signatures and only `[propext, Classical.choice, Quot.sound]` for the reviewed declarations.

The forbidden scan records exit `1` because `rg` found no matches; its evidence text explicitly reports that no forbidden tokens were found. This is a successful no-match scan, not a failed proof check.

The output root was seeded with 2,794 dependency files from the prior canonical conflict-degree target. The current `ActualQuestionMassBridge.olean` and Checks object were excluded from that copy, were absent before compilation, and main then Checks were compiled sequentially. Temporary/probe roots were excluded from `LEAN_PATH`. This is a fresh main-and-Checks build against a recorded precompiled dependency set. It is not a fresh rebuild or independent revalidation of all transitive dependencies, and evidence summaries must retain that qualification.

The compiler emitted only nonblocking maintenance warnings: deprecated `push_neg`, one unused `simp` argument, and the previously recorded unused `[Fintype X]` section variable for `conflict_degree_le`. None changes the frozen theorem statements or supports a broader claim.

## Exact generic result and assumptions

The terminal transcript confirms:

```lean
theorem bad_ordered_question_count_le
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    (row : E → Finset X) (D J : Nat)
    (hthree : ∀ e, (row e).card = 3)
    (hdegree : ∀ x,
      ((Finset.univ : Finset E).filter
        (fun e => x ∈ row e)).card ≤ D) :
    ((Finset.univ : Finset (Fin J → E)).filter
      (fun u => ¬ GoodOrderedQuestion row u)).card ≤
      J * (J - 1) * (1 + 3 * D + 9 * D^2) *
        (Fintype.card E) ^ (J - 1)
```

The assumptions are finite decidable coordinate and row types, three coordinates in every row, and at most `D` incident rows per coordinate. The theorem adds no positivity, pairwise-linearity, source-value, padding, probability, or hardness hypothesis. It handles `J = 0` and `J = 1` through the natural-number normalized expression and proves that no bad tuple exists in those cases, without adding `2 ≤ J`.

The supporting equivalence

```text
¬ GoodOrderedQuestion row u
  ↔ ∃ i j, i ≠ j ∧ rowConflict row (u i) (u j)
```

connects exactly the ordered injectivity/`GoodQuestion` failure to an ordered conflicting pair. The count then unions over the `J * (J - 1)` distinct ordered position pairs and applies the previously reviewed conflict-neighborhood bound. The conclusion is a count over the full finite function space. Calling it a “uniform ordered-tuple count” is appropriate because each function is counted once; calling it a probability theorem is not.

## The `D = 4`, `C = 157` boundary

Substituting `D = 4` into the generic conflict constant gives

```text
C = 1 + 3·4 + 9·4² = 157.
```

Accordingly, after separately discharging `hthree` and `hdegree` for the actual row-ID source, the generic theorem yields the count bound

```text
J · (J - 1) · 157 · |E|^(J - 1).
```

This arithmetic specialization does not itself appear as a frozen actual-source theorem in the reviewed increment. It also does not by itself prove a probability bound: formal conversion requires the total uniform sample-space cardinality, denominator/positivity handling, and the intended source/padding setup. `C = 157` is a conservative conflict-neighborhood constant, not a success probability, retained fraction, soundness gap, or number of required copies.

## Fixture audit

The fixtures stay within the generic counting boundary:

- the `Fin 0` and `Fin 1` examples exercise the small-`J` branches of `bad_ordered_question_count_le_of_conflict`;
- `mixedRows` exercises equality, direct-overlap, and cross-only conflict geometry, then instantiates the final count theorem with `D = 3`, `J = 2`;
- the earlier `repeatedOwner`, `threeRows`, and `badRows` checks retain the occurrence-degree and conflict-definition coverage.

The `mixedRows` example confirms that the final theorem can be instantiated on a finite fixture. It is not evidence for sharpness, for the actual-source `D = 4` specialization, or for `C = 157`. None of the fixtures samples tuples, computes a retained probability, conditions a law, or exercises disjoint-copy padding.

## Manuscript and ledger wording

The manuscript at `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`, requires further results at lines 1148–1158: disjoint-copy padding, an `O(J^2/N_outer)` illegitimate-tuple probability, preservation of value and degree, a conditioning-loss bound, and the retained-law marginal statement. The generic cardinality theorem supplies one numerator estimate toward that passage and proves none of those remaining claims by itself.

The planning ledger's frozen-task wording is appropriately bounded: it identifies the result as a generic count theorem, keeps positivity and padding outside the theorem, and leaves actual-source discharge to a subsequent specialization. At closeout it may record this exact generic count as complete, with the frozen source hashes, canonical seeded-dependency receipt, and three-lens reviews.

The **direct consumer is the actual-source specialization with `row := I.support`, `D = 4`, and conflict constant `157`**. After that, separate obligations must convert the count to an ordered-law probability, establish padding/positivity, and justify conditioning. The dependency path remains:

```text
rowId_incidence_card_le_four
  → conflict_degree_le
  → bad_ordered_question_count_le
  → actual-source D = 4 / C = 157 specialization
  → uniform bad-event probability
  → disjoint-copy padding, retained mass, and conditioning
  → actual-source question-law instantiation
```

## Required public wording

The strongest justified description is:

> Lean verifies a generic upper bound on the number of bad ordered row tuples in a finite three-uniform bounded-incidence system. With `D = 4`, its conservative conflict constant specializes arithmetically to `157`; the actual-source and probability/conditioning corollaries remain to be proved.

Do not say that good questions have sufficient probability, retained mass is positive, conditioning is certified, the actual source bridge is complete, the star construction is accepted, the randomized reduction is formalized, hardness is established, P versus NP is resolved, or the increment is novel or publication-ready.

## Material findings

1. The exact theorem is a generic cardinality bound over ordered functions, with its assumptions explicit and no hidden mass or source premise.
2. The small-`J` cases are covered without adding hypotheses; the fixtures exercise the intended combinatorial branches but do not establish the actual-source or probabilistic corollaries.
3. `D = 4` gives `C = 157` only as an arithmetic specialization of the generic conservative constant. Neither value is a probability or a completed source theorem here.
4. The canonical build evidence supports the frozen main and Checks targets while relying on a documented precompiled dependency seed.
5. The next accepted artifact should be the concrete actual-source specialization, followed by the probability, padding, and conditioning theorems. All reduction, hardness, P-versus-NP, novelty, and publication obligations remain open.

No public-claim promotion follows from this review.
