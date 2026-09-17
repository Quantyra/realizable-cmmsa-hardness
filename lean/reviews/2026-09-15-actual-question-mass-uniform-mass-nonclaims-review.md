# Uniform ordered bad-mass normalization: non-claims-boundary review

2026-09-15. Read-only review of the frozen rational normalization increment, its canonical seeded-dependency evidence, and the related dependency-ledger language. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment kernel-checks a rational upper bound for the bad fraction of the finite uniform space of ordered row-ID functions, under the explicit assumption that the actual row-ID type has positive cardinality. This is the correct normalization of the previously certified integer count.

It does not prove that the right-hand side is small or below one, give a complementary positive lower bound for good questions, construct copy padding, prove conditioning or resampling, establish the retained-law marginal, complete the source bridge, prove star acceptance, assemble a randomized reduction, establish hardness, resolve P versus NP, or establish novelty or publication readiness.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `414E679659581296AAEADB421729C0318D149428C6AC671EF217589EF55B433D` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `DF51EE8B4EA3BD46188AB71638DBD216EF852A2D57A247F15B0C9EE79B45A502` | Matches the routed freeze. |
| `research/evidence/2026-09-15-actual-question-mass-uniform-mass-fresh-run/artifact-hashes.txt` | `D42A3A37835210C8053884563008C7131DF81535BF5BA2F226B14D0B7373636F` | Matches the evidence's manifest pointer. |

The canonical evidence records stable source hashes, main and Checks exit codes `0`, empty stderr, and newly emitted object hashes `D73F668AF001299D08991A8AC8C8A4B89CD8A10E292D3B0E9975AFF40AB0C6EF` and `7A7FC8438937806A724DA9E1D5A16BEEA6C38BD91F65E21DCB449355EE0859CF`. The preserved axiom summary reports only `[propext, Classical.choice, Quot.sound]` and no user-declared axioms. The forbidden scan is clean.

The output root was seeded with 2,794 dependency files from the prior canonical bad-ordered-count target. The current main and Checks objects were excluded, absent before compilation, and emitted by sequential main-then-Checks compilation. Temporary and probe roots were excluded from `LEAN_PATH`. This is a fresh main-and-Checks build against a recorded precompiled dependency set. It is not a fresh rebuild or independent revalidation of all transitive dependencies, and summaries must retain that caveat.

The compiler emitted only maintenance warnings: deprecated `push_neg`, unused `simp` arguments, the previously recorded unused `[Fintype X]` on the generic conflict theorem, and the local `letI` style suggestion. None changes the reviewed theorem or supports a broader claim.

## Exact theorem and assumption

The Checks transcript confirms:

```lean
theorem actual_bad_ordered_question_uniform_mass_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) (hrows : 0 < Fintype.card I.RowId) :
    (((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card : ℚ) /
        (Fintype.card (Fin J → I.RowId) : ℚ) ≤
      ((J * (J - 1) * 157 : Nat) : ℚ) /
        (Fintype.card I.RowId : ℚ)
```

The only new premise is `hrows`, positivity of the actual row-ID cardinality. It guarantees positivity of both denominators through `Fintype.card_fun`; the proof then cross-multiplies and invokes `actual_bad_ordered_question_count_mul_rowCard_le`. It adds no padding, size-growth, retained-law, source-value, or hardness premise.

The left side is the rational cardinality of the bad subset divided by the cardinality of the full finite function space `Fin J → I.RowId`. It therefore represents the bad fraction under the uniform distribution on all ordered functions, equivalently independent ordered row-ID draws with replacement. No probability-measure or sampler object is constructed by this theorem, so public wording should say “rational uniform bad fraction” unless a later bridge identifies it with the project's probability API.

The right side is

```text
157 · J · (J - 1) / |I.RowId|.
```

Natural-number multiplication is cast to `ℚ` only after forming `J * (J - 1) * 157`. The coefficient `157` remains the conservative conflict-count constant. It is not a probability, a success fraction, a soundness gap, a copy count, or a claim of tightness.

## What `hrows` does and does not provide

`hrows` rules out an empty row-ID universe and makes the displayed division legitimate. It does not lower-bound `|I.RowId|` strongly enough to make the right side less than one or any manuscript tolerance. For example, positivity alone gives no relation between the row count and `157 * J * (J - 1)`.

A later actual-source or padding theorem must discharge `hrows` and prove the stronger quantitative row-count condition needed for small bad mass. The present theorem is valid for `J = 0` and `J = 1`; in those cases the natural-number factor `J * (J - 1)` is zero, consistent with the previously proved absence of bad tuples.

## Fixture audit

The `repeatedOwner` fixture explicitly proves its row-cardinality positivity by exhibiting `Sum.inl 0`. It instantiates the rational theorem for `J = 0`, `1`, and `2`, while the companion cross-multiplied fixtures cover the same cases. These checks exercise positivity, small-`J` normalization, and the dependent actual row-ID type.

They do not compute a nontrivial bad fraction, establish that the upper bound is below one, demonstrate asymptotic decay, construct copies, condition a distribution, or verify a retained sampler marginal. Repeated ownership also does not merge occurrence IDs; the fixture remains aligned with the actual occurrence-indexed count.

## Retained-mass and manuscript boundary

The theorem is one normalization step toward the manuscript discussion at lines 1148–1158 of `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`. That passage additionally requires:

- sufficiently many disjoint copies to make the bad fraction at most the selected tolerance;
- preservation of source value and degree under those copies;
- a positive retained event and the `1 / (1 - a)` conditioning-loss estimate;
- proof that clique resampling preserves the uniform law on legitimate questions;
- the ordered-to-subset/question-law connection used by the star construction.

None of these follows from `actual_bad_ordered_question_uniform_mass_le` alone. In particular, an upper bound whose right side may exceed one is still mathematically valid but does not establish useful retained mass.

## Ledger and direct consumer

The planning ledger's pre-freeze wording is appropriately bounded: it describes rational normalization under exactly the positive row-cardinality assumption and names complementary good mass, padding, conditioning, and pushforward as later obligations.

At closeout the ledger may record this exact rational fraction theorem as complete with the frozen source hashes, canonical seeded-dependency receipt, and three-lens reviews. The actual-source assumption bridge must remain conditional.

The **direct consumer is a complementary good-mass lower bound combined with a quantitative row-count or disjoint-copy padding theorem**. The remaining path is:

```text
actual_bad_ordered_question_uniform_mass_le
  → quantitative row-count growth / disjoint-copy padding
  → bad mass below the selected tolerance
  → positive retained good mass and conditioning-loss control
  → retained-law marginal and ordered-to-subset pushforward
  → actual-source question-law instantiation
```

## Required public wording

The strongest justified description is:

> Assuming the actual row-ID universe is nonempty, Lean verifies that the rational bad fraction for uniform ordered row-ID functions is at most `157·J(J-1)/|RowId|`. Making this bound small and proving padding, retained mass, conditioning, and the retained law remain open.

Do not say that sufficient good mass, successful conditioning, the complete source law, star acceptance, a randomized reduction, hardness, P versus NP, novelty, or publication readiness has been proved.

## Material findings

1. The displayed ratio is the correct rational normalization of the full finite ordered-function count.
2. The explicit `hrows` assumption is necessary for the proof's denominator positivity and is not discharged generically here.
3. Positivity alone does not make the `157·J(J-1)/|RowId|` bound useful or below one.
4. The fixtures cover `J = 0`, `1`, and `2` with an explicit positive actual row universe but make no retained-mass claim.
5. The canonical receipt certifies the frozen main and Checks targets against documented seeded dependencies, not a full transitive rebuild.
6. Padding, sufficient mass, conditioning, retained-law identity, source completion, reduction, hardness, P-versus-NP, novelty, and publication obligations remain open.

No public-claim promotion follows from this review.
