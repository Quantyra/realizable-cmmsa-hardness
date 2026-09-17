# Uniform ordered good-mass complement: non-claims-boundary review

2026-09-15. Read-only review of the frozen complement increment, its canonical seeded-dependency evidence, and the related dependency-ledger language. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment kernel-checks the exact complement of the previously certified rational bad-fraction bound. Under positive actual row-ID cardinality, it lower-bounds the uniform ordered good fraction by `1 - 157·J(J-1)/|I.RowId|`.

That lower bound may be zero or negative. The theorem does not prove strict positivity, sufficient retained mass, a quantitative row-count threshold, source-preserving copy padding, conditioning or resampling, the retained-law marginal, completion of the source bridge, star acceptance, a randomized reduction, hardness, P versus NP, novelty, or publication readiness.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `A7D5A591E56A2334FC2FF83A366461B5D0E8325709F6AC4A24EB54C7BA95B969` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `A5BA00342736D44D411927B725A5C0E7A9378266BF3CBA48137DF76A08BBF4DD` | Matches the routed freeze. |
| `research/evidence/2026-09-15-actual-question-mass-uniform-good-mass-fresh-run/artifact-hashes.txt` | `5088079C7957AE6BB18632F6131ABD5396BFBB9EB5E930B6253B56E25FF41383` | Matches the routed manifest hash and evidence pointer. |

The canonical evidence records stable source hashes, main and Checks exit codes `0`, empty stderr, and newly emitted object hashes `E8C7E557F510FEE98634542EB0B30458327B419534E4F300CDA98FCD409F5DEC` and `8A7EEA0350086D15D5A9A370DACECF3FBC962508F1E74256A9A5734AC44EAB15`. The preserved axiom summary reports only `[propext, Classical.choice, Quot.sound]` and no user-declared axioms. The forbidden scan is clean.

The output root was seeded with 2,794 dependency files from the prior canonical uniform-bad-mass target. The current main and Checks objects were excluded, absent before compilation, and emitted by sequential main-then-Checks compilation. Temporary and probe roots were excluded from `LEAN_PATH`. This is a fresh main-and-Checks build against a recorded precompiled dependency set. It is not a fresh rebuild or independent revalidation of all transitive dependencies, and summaries must preserve that caveat.

The compiler emitted only previously documented maintenance warnings concerning deprecated `push_neg`, unused `simp` arguments, the unused `[Fintype X]` on the generic conflict theorem, and the local `letI` style suggestion. None changes the reviewed theorem or justifies a broader claim.

## Exact theorem and assumptions

The Checks transcript confirms:

```lean
theorem actual_good_ordered_question_uniform_mass_ge
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) (hrows : 0 < Fintype.card I.RowId) :
    1 - ((J * (J - 1) * 157 : Nat) : ℚ) /
        (Fintype.card I.RowId : ℚ) ≤
      (((Finset.univ : Finset (Fin J → I.RowId)).filter
        (fun u => GoodOrderedQuestion I.support u)).card : ℚ) /
        (Fintype.card (Fin J → I.RowId) : ℚ)
```

The only non-structural premise remains `hrows`, positivity of the actual row-ID cardinality. It makes the uniform function-space denominator positive and permits the rational complement calculation. The theorem introduces no smallness, padding, value-preservation, conditioning, retained-law, or hardness assumption.

The helper `ordered_good_bad_card_add_eq_total` exactly partitions the full finite function space into `GoodOrderedQuestion` and its negation. The proof rewrites the good fraction as one minus the bad fraction, then applies `actual_bad_ordered_question_uniform_mass_le`. This justifies the displayed lower bound for the rational uniform fraction over ordered functions.

No probability-measure or sampler object is constructed. “Uniform ordered good fraction” is accurate shorthand for the finite cardinality ratio; a claim about the project's probability or sampler API still requires an explicit bridge.

## Nonpositivity boundary

The left side is useful only when the row count is sufficiently large. From `hrows` alone, the quantity

```text
1 - 157·J(J-1)/|I.RowId|
```

may be negative. Even equality to zero would not prove a positive retained event. Strict positivity requires a separate condition equivalent to a sufficiently strong inequality such as `157·J(J-1) < |I.RowId|`, together with the intended rational conversion.

The theorem does not clamp the lower bound at zero, and it must not be described as proving retained-mass positivity. The actual good fraction is of course nonnegative as a cardinality ratio, but that elementary fact does not turn a possibly nonpositive certified lower bound into the positive quantitative estimate needed for conditioning.

For `J = 0` and `J = 1`, the natural-number factor `J * (J - 1)` is zero, so the displayed lower bound is one. Those edge cases do not supply the large-row estimate needed for the manuscript's fixed positive `J` regime.

## Fixture audit

The `repeatedOwner` fixtures instantiate the complement theorem for `J = 0`, `1`, and `2` using the explicit witness `repeatedOwner_rowCard_pos`. They test the complement signature, the small-`J` arithmetic, and the dependent actual row-ID type.

The `J = 2` fixture does not assert that its lower bound is positive, compute the exact good fraction, show sharpness, or establish a padding effect. None of the fixtures constructs copies, verifies source-value preservation, conditions a distribution, or proves a retained sampler marginal.

## Manuscript and retained-law boundary

The theorem is one algebraic step toward lines 1148–1158 of `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`. That passage additionally requires:

- a source-preserving disjoint-copy construction that grows the row universe while preserving the value and degree bounds;
- a proof that the resulting bad fraction is below the chosen tolerance and hence the good event has strictly positive mass;
- the `1 / (1 - a)` conditioning-loss bound;
- preservation of the uniform legitimate-question marginal under clique resampling;
- the ordered-to-subset/question-law connection needed by the star construction.

None follows from the complement identity alone.

## Ledger and direct consumer

The planning ledger's pre-freeze wording is appropriately bounded: it explicitly states that useful strict positivity requires a later smallness or padding condition and warns against inferring positivity when the coefficient exceeds one.

At closeout the ledger may record the exact complement lower bound as complete with the frozen source hashes, canonical seeded-dependency receipt, and three-lens reviews. The actual-source assumption bridge must remain conditional.

The **direct consumer is a source-preserving disjoint-copy padding theorem that makes `157·J(J-1)/|I.RowId| < 1`**, followed by a strict retained-mass theorem. The remaining path is:

```text
actual_good_ordered_question_uniform_mass_ge
  → source-preserving disjoint-copy padding and row-count growth
  → strict positivity / selected retained-mass threshold
  → conditioning-loss control
  → retained-law marginal and ordered-to-subset pushforward
  → actual-source question-law instantiation
```

## Required public wording

The strongest justified description is:

> Assuming a nonempty actual row-ID universe, Lean lower-bounds the uniform ordered good fraction by `1 - 157·J(J-1)/|RowId|`. This lower bound may be nonpositive; padding, strict retained mass, conditioning, and the retained law remain open.

Do not say that good questions already have positive or sufficient mass, conditioning is certified, the source bridge is complete, the star construction is accepted, a randomized reduction is formalized, hardness is established, P versus NP is resolved, or the increment is novel or publication-ready.

## Material findings

1. The finite good/bad partition and rational complement are correctly represented at the claim boundary.
2. `hrows` provides denominator positivity only; it does not supply the quantitative row-count inequality needed for a positive lower bound.
3. The lower bound is intentionally unclamped and may be negative. It must not be reported as retained-mass positivity.
4. The fixtures cover the complement theorem at `J = 0`, `1`, and `2` but do not test padding or strict positivity.
5. The canonical receipt certifies the frozen main and Checks targets against documented seeded dependencies, not a full transitive rebuild.
6. Padding, strict retained mass, conditioning, retained-law identity, source completion, reduction, hardness, P-versus-NP, novelty, and publication obligations remain open.

No public-claim promotion follows from this review.
