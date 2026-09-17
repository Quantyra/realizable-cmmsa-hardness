# Proof-adversarial review: uniform ordered bad mass

**Verdict: GO-WITH-NOTES.** The frozen increment proves the exact rational normalization of the previously certified actual bad-ordered-tuple count. For every actual occurrence allocation with a nonempty row-ID type, it bounds the fraction of all ordered functions `Fin J → I.RowId` that fail `GoodOrderedQuestion I.support` by

`(J * (J - 1) * 157 : Nat) / Fintype.card I.RowId`.

The cross-multiplied bridge is correct for every natural `J`, including its explicit `J = 0` branch, and the rational theorem uses the denominator hypotheses in the correct orientation. I found no cast error, truncated-subtraction error, hidden cancellation, missing premise, weakened event, or certification defect. The notes concern logical minimality of `hrows`, the limited role of the fixtures, and the still-open complementary good-mass, padding, and conditioning consumers.

## Frozen artifacts and certification

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `414E679659581296AAEADB421729C0318D149428C6AC671EF217589EF55B433D` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `DF51EE8B4EA3BD46188AB71638DBD216EF852A2D57A247F15B0C9EE79B45A502` |
| canonical `artifact-hashes.txt` | `D42A3A37835210C8053884563008C7131DF81535BF5BA2F226B14D0B7373636F` |

The canonical evidence directory is `research/evidence/2026-09-15-actual-question-mass-uniform-mass-fresh-run/`. I independently recomputed all 30 byte counts and SHA-256 values in `artifact-hashes.txt`; every entry matches, and the artifact manifest itself has the recorded hash above. The current main and Checks files match the routed frozen hashes, and the before/after records show that both hashes stayed stable during certification.

Main and Checks both exited `0` with empty stderr. Their newly emitted object hashes are respectively `D73F668AF001299D08991A8AC8C8A4B89CD8A10E292D3B0E9975AFF40AB0C6EF` and `7A7FC8438937806A724DA9E1D5A16BEEA6C38BD91F65E21DCB449355EE0859CF`. Neither current object existed in the isolated target before compilation, and main was compiled before Checks. The target was seeded with the recorded 2,794-file dependency tree from the preceding canonical count build while explicitly excluding the current main and Checks objects. The receipt records the Lean `v4.34.0-rc2` executable, package revisions and manifests, dependency-seed manifest, exact commands, `LEAN_PATH`, output inventory, and object hashes; no temporary or probe root occurs in `LEAN_PATH`. This certifies a fresh build of the changed main and Checks against pinned precompiled dependencies, rather than a source rebuild of every transitive dependency.

The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and user-declared axioms. The Checks transcript gives only `propext`, `Classical.choice`, and `Quot.sound` for the reviewed declarations and their checked dependencies. Compiler output contains maintenance warnings about deprecated `push_neg`, unused `simp` arguments, a pre-existing unused section variable, and a `letI` style suggestion; none changes proof content.

## Exact cross-multiplied theorem

The first new bridge is:

```lean
theorem actual_bad_ordered_question_count_mul_rowCard_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J : Nat) :
    ((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card *
        Fintype.card I.RowId ≤
      (J * (J - 1) * 157) *
        Fintype.card (Fin J → I.RowId)
```

It has no new mathematical assumption. Let `B` be the filtered bad cardinality, `R = Fintype.card I.RowId`, and `C = J * (J - 1) * 157`. The consumed theorem is exactly

`B ≤ C * R^(J - 1)`.

For `J > 0`, monotonicity under multiplication by `R` gives `B * R ≤ C * R^(J - 1) * R`. The identity

`R^(J - 1) * R = R^J`

is justified from `1 ≤ J`, and `Fintype.card_fun` identifies `R^J` with `Fintype.card (Fin J → I.RowId)`. The associativity rewrite preserves the factor order. This argument does not cancel `R` and therefore does not require `R > 0`.

The explicit `J = 0` branch is necessary because natural subtraction makes `J - 1 = 0`, so the power extension used in the positive branch is unavailable. The prior count bound specializes to `B ≤ 0`; `Nat.eq_zero_of_le_zero` therefore gives `B = 0`, and both sides of the cross-multiplied target reduce to zero. This is valid even if the row-ID type is empty. At `J = 1`, the positive branch applies, `J - 1 = 0`, and the zero coefficient again forces the bad set to be empty.

## Exact rational theorem

The exported normalization is:

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

The elaborated declaration in `checks.stdout` matches this source signature. It uses the same actual row-ID function space, the same bad predicate, and the same natural-number coefficient before casting. No alternate probability space, quotient of repeated row values, or supplied source promise appears.

`exact_mod_cast hrows` correctly produces positive rational row cardinality `hR`. Rewriting the tuple-space cardinality with `Fintype.card_fun` and applying `pow_pos hR` proves positive left denominator `hT` for every `J`, including `J = 0`. Mathlib's

```lean
div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) :
  a / b ≤ c / d ↔ a * d ≤ c * b
```

is invoked as `(div_le_div_iff₀ hT hR).2`. Thus the generated goal is exactly

`badCard * rowCard ≤ coefficient * tupleCard`,

with the left denominator passed first and the right denominator second. `exact_mod_cast` then transports the already proved natural-number cross inequality into `ℚ`; it neither reverses the inequality nor performs a cancellation.

## Sufficiency and minimality of `hrows`

`hrows : 0 < Fintype.card I.RowId` is sufficient and semantically appropriate. It says the base row universe is nonempty, makes `Fin J → I.RowId` nonempty for every `J`, and ensures both displayed denominators are positive. Under this premise, the left ratio is literally the fraction of the finite uniform ordered-function sample space occupied by the bad event.

The premise is not logically minimal for the bare inequality in Lean. An `Instance 0 0` can have empty `RowId`, rational division is totalized at zero, and the displayed inequality still reduces to a true zero-denominator identity in that degenerate case: for `J = 0` the unique empty function is good, while for `J > 0` there are no functions. The present proof deliberately uses strict positivity and does not discharge that algebraic edge case. This is a scope restriction, not a correctness problem, and retaining `hrows` avoids describing a division-by-zero term as a uniform probability. A later source or padding theorem must establish this premise for the instances it supplies.

`hrows` supplies no quantitative lower bound beyond one. It does not show that `157 * J * (J - 1) / R < 1`, much less that it meets the manuscript tolerance.

## Fixture audit

The Checks module proves `repeatedOwner_rowCard_pos` by exhibiting the actual row ID `Sum.inl 0`. It then instantiates both the cross-multiplied theorem and the rational theorem at `J = 0`, `J = 1`, and `J = 2`. These are useful signature regressions: they confirm the dependent row-ID type, positivity premise, and all small-`J` theorem applications elaborate against the frozen declarations.

The fixtures do not compute exact bad-set cardinalities or rational values. The generic main proof, rather than fixture reduction, is the kernel-checked evidence for the `J = 0` branch and power arithmetic. `J = 2` exercises the first nontrivial index size at the declaration boundary but does not show the upper bound is sharp or below one. This is adequate for the stated fewer-stronger-fixtures policy because every meaningful theorem branch is present in main and the three boundary applications are compiled in Checks.

## Direct good-mass consumer

The next theorem should partition the full tuple space into good and bad functions and consume this exact normalization to prove the complementary bound

```text
1 - (157 * J * (J - 1) / Fintype.card I.RowId)
  ≤
  card {u | GoodOrderedQuestion I.support u}
    / Fintype.card (Fin J → I.RowId),
```

under the same `hrows` premise. An equivalent parameterized form may assume the bad fraction is at most `a` and conclude good fraction at least `1 - a`. This complement theorem alone will not prove positivity: its next consumer must obtain a quantitative row-count bound, likely through the manuscript's disjoint-copy padding, that makes the bad bound at most `a < 1`. Only then may the development construct or characterize conditioning, charge the factor `1 / (1 - a)`, and prove the retained-law and ordered-to-subset pushforward identities.

The manuscript passage at lines 1148–1158 additionally requires that padding preserve source value and degree, that the copy count remain polynomially harmless, and that clique resampling preserve the uniform legitimate-question law. None is contained in this normalization theorem.

## Review disposition

Accept both `actual_bad_ordered_question_count_mul_rowCard_le` and `actual_bad_ordered_question_uniform_mass_le` as completed. Their arithmetic, casts, denominator orientation, edge branches, and source event are correct, and their canonical seeded-dependency certification supports the frozen statements.

**GO-WITH-NOTES.** The notes do not expose a defect in either theorem. They record that `hrows` is semantically useful but stronger than logical necessity for the totalized rational inequality, that the fixtures are application checks rather than exact numerical evaluations, and that good-mass positivity, padding, conditioning, retained-law uniformity, actual-source completion, and every later reduction or hardness claim remain open.
