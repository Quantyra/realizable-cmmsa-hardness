# Proof-adversarial review: uniform ordered good mass

**Verdict: GO-WITH-NOTES.** The frozen increment proves the exact complementary lower bound for the uniform mass of actual ordered row-ID functions satisfying `GoodOrderedQuestion`. The good and bad filters partition the same finite function space, the rational complement algebra is valid under the stated positive-row premise, and the previously certified bad-mass inequality is used in the correct direction. I found no mismatch of decidability instances, denominator, cast, event, or inequality orientation. The notes concern the strength and downstream discharge of `hrows`, the limited numerical content of the fixtures, and the still-open padding and conditioning bridges.

## Frozen artifacts and certification

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `A7D5A591E56A2334FC2FF83A366461B5D0E8325709F6AC4A24EB54C7BA95B969` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `A5BA00342736D44D411927B725A5C0E7A9378266BF3CBA48137DF76A08BBF4DD` |
| canonical `artifact-hashes.txt` | `5088079C7957AE6BB18632F6131ABD5396BFBB9EB5E930B6253B56E25FF41383` |

The canonical evidence directory is `research/evidence/2026-09-15-actual-question-mass-uniform-good-mass-fresh-run/`. I independently recomputed the byte count and SHA-256 value of every one of the 29 entries in `artifact-hashes.txt`; all entries match. The current main and Checks files match the routed frozen hashes, and the before/after evidence records stable source hashes during certification.

Main and Checks exited `0` with empty stderr. Their fresh object hashes are respectively `E8C7E557F510FEE98634542EB0B30458327B419534E4F300CDA98FCD409F5DEC` and `8A7EEA0350086D15D5A9A370DACECF3FBC962508F1E74256A9A5734AC44EAB15`. Neither current object existed in the isolated target before compilation, and main was compiled before Checks. The target was seeded with the recorded 2,794-file dependency tree from the preceding certified uniform-bad-mass build while excluding the current main and Checks objects. The receipt records Lean `v4.34.0-rc2`, package revisions and manifests, seed and output inventories, exact commands, and `LEAN_PATH`; no temporary or probe root occurs in `LEAN_PATH`. This is a fresh main-and-Checks build against pinned precompiled dependencies, not a source rebuild of every transitive dependency.

The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and user-declared axioms. The exact Checks transcript reports only `propext`, `Classical.choice`, and `Quot.sound` for the reviewed declarations and their dependencies.

## Exact theorem

The new exported theorem is:

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

The elaborated declaration in `checks.stdout` matches this signature. It concerns all ordered functions `Fin J → I.RowId`, sampled uniformly by cardinality, and the exact predicate `GoodOrderedQuestion I.support`. It adds only the explicit row-cardinality premise `hrows`; it does not assume the displayed lower bound is positive, a copy count, a source-value promise, or any conditioning result.

## Complement-card identity and decidability coherence

The supporting theorem

```lean
theorem ordered_good_bad_card_add_eq_total ... :
  card (filter GoodOrderedQuestion univ) +
    card (filter (¬ GoodOrderedQuestion) univ) =
      Fintype.card (Fin J → E)
```

is a direct specialization of `Finset.card_filter_add_card_filter_not`, followed only by `Finset.card_univ`. This is exactly the finite partition needed: every function either satisfies the proposition or its negation, the two parts are disjoint, and their union is the full function space.

There is no `DecidablePred` coherence defect. The module installs `Classical.propDecidable` locally, and the identity theorem introduces `classical` before constructing both filters and applying Mathlib's complement lemma. The consumer also introduces `classical`; its `exact_mod_cast` application elaborates the same proposition on the same `Finset.univ`. The successful kernel-checked transport into `hsum` confirms the two filter expressions are definitionally/propositionally aligned. No separately supplied Boolean test or alternate membership decision procedure occurs in this increment.

## Rational complement algebra

Write `G` for the good cardinality, `B` for the bad cardinality, `T` for `Fintype.card (Fin J → I.RowId)`, and

```text
A = (J * (J - 1) * 157 : Nat) / Fintype.card I.RowId.
```

`hsum` is exactly `G + B = T` after casting from `Nat` to `ℚ`. `linarith [hsum]` derives `G = T - B`; this use is valid over `ℚ` and introduces no natural truncated subtraction. The proof then rewrites

```text
(T - B) / T = T / T - B / T
```

with `sub_div`, and rewrites `T / T = 1` using `div_self` after proving `T > 0`. Thus `hgood` is the exact identity

```text
G / T = 1 - B / T.
```

The preceding theorem gives `B / T ≤ A`. Applying `sub_le_sub_left hbad 1` correctly yields

```text
1 - A ≤ 1 - B / T,
```

which, by `hgood.symm`, is the stated lower bound on `G / T`. The inequality direction is therefore correct: a larger upper bound on bad mass produces a smaller lower bound on good mass. There is no cancellation across an unknown sign and no cast of rational subtraction back into `Nat`.

## Positivity and use of `hrows`

The only strict-positivity assumption is visible in the theorem signature:

```lean
hrows : 0 < Fintype.card I.RowId.
```

It is used in two legitimate places. First, it is passed to `actual_bad_ordered_question_uniform_mass_le`. Second, `exact_mod_cast hrows` gives positive rational base cardinality, from which `Fintype.card_fun` and `pow_pos` establish `0 < T` for every `J`. That proof justifies `T ≠ 0` in `div_self`.

The theorem does not implicitly assume

```text
157 * J * (J - 1) < Fintype.card I.RowId.
```

Consequently its left side may be zero or negative, and the result alone need not provide useful retained mass. This is intentional: a padding theorem must later make the quantitative error strictly below one. `hrows` is stronger than the bare totalized-rational identity would require in degenerate zero-denominator cases, but it is the appropriate premise for interpreting the quotient as a uniform probability. A downstream actual-source theorem must prove it rather than silently infer it for `Instance 0 0`.

## Small-`J` fixtures

Checks instantiates both `ordered_good_bad_card_add_eq_total` and the actual good-mass theorem. For `repeatedOwner`, it separately proves row-cardinality positivity by exhibiting `Sum.inl 0`, then applies the new theorem at `J = 0`, `J = 1`, and `J = 2`.

- At `J = 0`, `J * (J - 1)` is zero despite truncated natural subtraction, the unique empty function is good, and the good mass is one.
- At `J = 1`, the coefficient is again zero and every one-coordinate tuple is injective with a singleton image, so the good mass is one.
- At `J = 2`, the fixture verifies the first nontrivial theorem application and its dependent row-ID types.

These are compilation and signature fixtures. They do not normalize the exact cardinalities to numerals, show sharpness of `157`, or demonstrate a positive lower bound in the `J = 2` instance. In particular, the `J = 2` application can remain mathematically true with a negative displayed lower bound. The generic theorem proof, rather than fixture computation, is the evidence for complement arithmetic and all `J`.

## Direct padding consumer

Accept `ordered_good_bad_card_add_eq_total` and `actual_good_ordered_question_uniform_mass_ge` as completed. Their next structural consumer must construct the manuscript's disjoint-copy padding and establish, for the copied instance or copied semantic row system:

1. the copied row count, including positivity and multiplication by the copy factor;
2. three-element support and incidence at most four after copying;
3. disjointness of variables across distinct copies;
4. preservation of the source YES/NO value and degree promises;
5. a concrete polynomially bounded copy count `K` for which
   `157 * J * (J - 1) / |RowId_padded| ≤ a < 1`.

The accepted theorem can then yield `Pr[GoodOrderedQuestion] ≥ 1 - a > 0`. Only after that may conditioning be defined and its loss bounded, followed by the ordered-to-subset pushforward and the later clique-resampling marginal. The current theorem does not itself prove padding, positivity of retained mass, conditioning, sampling efficiency, source completion, actual-star acceptance, randomized hardness, or any P-versus-NP conclusion.

## Disposition

**GO-WITH-NOTES.** The exact complement identity, decidability alignment, rational casts and divisions, use of `hrows`, inequality direction, and `J = 0/1/2` applications are sound. The notes are downstream obligations: discharge row positivity on the padded source, make the lower bound quantitatively positive, and prove the padding/value-preservation and conditioning bridges before treating the actual-source question law as complete.
