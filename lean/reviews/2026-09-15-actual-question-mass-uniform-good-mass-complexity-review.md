# Complexity/manuscript review: actual uniform good-question mass

Date: 2026-09-15  
Lens: complexity theory and manuscript dependency  
Mode: read-only review after source freeze; no Lean source was edited or compiled by this reviewer

## Verdict

**GO-WITH-NOTES.** The frozen theorem is the correct complementary lower bound for the uniform ordered-row law, and it closes the ledger's exact `actual_good_ordered_question_uniform_mass_ge` obligation without adding a structural assumption beyond positive row cardinality. It becomes quantitatively useful only after a separate padding theorem makes

```text
157 * J * (J - 1) / |I.RowId|
```

smaller than the desired exclusion allowance. The present result does not itself prove positive retained mass, construct or preserve disjoint copies, define a conditioned law, transfer the ordered law to legitimate equation subsets, prove the clique-resampling marginal, or preserve source value. Those are live manuscript dependencies rather than qualifications to the correctness of this increment.

## Frozen artifacts and certification evidence

- Main source: `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean`, SHA-256 `A7D5A591E56A2334FC2FF83A366461B5D0E8325709F6AC4A24EB54C7BA95B969`.
- Checks source: `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean`, SHA-256 `A5BA00342736D44D411927B725A5C0E7A9378266BF3CBA48137DF76A08BBF4DD`.
- Evidence directory: `research/evidence/2026-09-15-actual-question-mass-uniform-good-mass-fresh-run/`.
- `artifact-hashes.txt` has SHA-256 `5088079C7957AE6BB18632F6131ABD5396BFBB9EB5E930B6253B56E25FF41383`, exactly the digest recorded by `artifact-hashes-manifest.sha256`.
- The evidence records main exit `0`, Checks exit `0`, source stability, and fresh target objects `E8C7E557...5DEC` and `8A7EEA03...AB15`. The target was seeded with previously certified dependencies while excluding the two target objects; this certifies the changed main-and-Checks increment, not a from-zero rebuild of the whole project.
- The forbidden scan found no `sorry`, `admit`, `native_decide`, or user `axiom`. The reported axiom profile is only `propext`, `Classical.choice`, and `Quot.sound`.
- Checks exercise the exact theorem at `J = 0`, `J = 1`, and `J = 2` on an occurrence-sensitive fixture. These are useful elaboration and boundary checks; the general theorem, rather than the fixtures, supplies the mathematical coverage.
- Canonical manuscript inspected: `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`.

## Exact theorem and mathematical meaning

The reviewed declaration is

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

The denominator is the cardinality of all ordered length-`J` row tuples sampled independently and uniformly with replacement. The numerator counts exactly those tuples whose entries are injective and whose image satisfies both clauses of `ActualStarQuestionSupport.GoodQuestion`: pairwise disjoint selected supports and the global no-cross condition.

The proof uses the exact finite partition into good and non-good tuples and the already certified upper bound on the non-good fraction. If `p_bad` and `p_good` denote these two rational fractions, the partition proves `p_good = 1 - p_bad`; the prior result proves

```text
p_bad ≤ 157 * J * (J - 1) / |I.RowId|.
```

Subtracting the latter inequality from one gives the reviewed result with the correct direction. Positivity of the full function-space denominator follows from `hrows`. No probabilistic independence is silently used after the initial product-uniform tuple law.

For `J = 0` and `J = 1`, the coefficient is zero and the theorem gives good mass at least one, consistent with the absence of a distinct conflicting pair. For general `J`, the displayed lower bound is deliberately not clamped at zero. It can therefore be true but uninformative when the row universe is too small. In particular:

- strict positive retained mass follows from the bound only when `|I.RowId| > 157 J(J-1)`;
- bad mass at most `1/4` follows if `|I.RowId| ≥ 4 * 157 J(J-1)`;
- the manuscript target `a ≤ min(tau/100, 1/4)` requires a separate exact inequality making `157 J(J-1)/|I.RowId|` at most that target.

Thus this theorem supplies the right quantitative input to padding, but does not itself establish that an arbitrary constructed source has even one legitimate `J`-question. The positive-cardinality premise also has to be discharged by the concrete source route; copying cannot repair an empty starting row universe.

## Manuscript dependency discharged

Lines 1148-1154 of the manuscript require an `O(J^2/N_outer)` bound on discarded illegitimate tuples after enough disjoint copies. The reviewed theorem establishes the complementary form of precisely this scale for the current occurrence-row representation:

```text
uniform good ordered-row mass ≥ 1 - 157 J(J-1)/|I.RowId|.
```

The constant `157` comes from the separately certified degree-four, three-uniform conflict-neighborhood bound. Row occurrences, rather than deduplicated row values, remain the sample points. This is important because the actual construction may have identical owner labels or repeated row values whose occurrences must retain distinct probability mass.

The result is sufficient as the counting estimate used by the manuscript once the formal source construction proves that its padded row universe is the universe sampled here. It is not yet an identification with the manuscript's full outer-game law. Contract 1 at manuscript lines 158-170 samples `J` equations independently and then performs coordinate retention and shared advice. Contract 2 at lines 171-187 keeps legitimate equation sets and adds transverse-space and equivalence-class sampling. The current theorem covers only the initial ordered equation tuple and its legitimacy event.

## Exact remaining padding and value-preservation work

The next high-risk bridge should construct disjoint copies at the actual source level, before later consumers assume their existence. At minimum it must prove all of the following for an explicit copy count `K`:

1. **Typed disjoint-copy constructor.** Construct the copied variables and rows with a copy index so rows from different copies have disjoint support and preserve the original RHS. The result must feed the existing `ActualOccurrenceAllocation.Instance` path or come with an exact isomorphism to the incidence representation consumed here.
2. **Row-cardinality growth.** Prove the precise cardinality formula or a sufficient lower bound, normally linear in `K`, and discharge positive row cardinality. This theorem must be strong enough to choose a fixed `K` satisfying the rational target `157 J(J-1)/|RowId_padded| ≤ min(tau/100,1/4)`.
3. **Local geometry preservation.** Prove support cardinality three, pairwise-linearity/no-repeated-pair, and incidence degree at most four for the padded instance. Cross-copy incidences must be empty. These facts should be derived, not added as certificate assumptions.
4. **Source value preservation.** For the exact source objective used by the outer theorem, prove that the optimum satisfied fraction of `K` identical disjoint copies equals that of one copy. One inequality copies an optimal assignment; the reverse inequality averages the per-copy values. The theorem must cover both stored RHS values and the occurrence/equality rows introduced by regularization, or state and verify the order in which copying and regularization commute sufficiently for the manuscript argument.
5. **Encoded reduction preservation.** Prove that the copied source remains polynomially constructible, that `K` depends only on the already fixed manuscript parameters, and that encoded length remains polynomial. Because `J`, `tau`, and `K` are fixed constants in the claimed theorem, this does not require a uniform exponent when they vary with the input.

There is a representation issue to freeze before implementation: the manuscript writes `N_outer` for the outer equation count, whereas this theorem divides by the cardinality of the regularized occurrence universe `I.RowId`, which includes original and gadget rows. The next theorem must explicitly identify the game law with uniform sampling from that exact universe, or prove the comparison that transports the outer source value and counting estimate to it. Merely observing that the regularized universe is larger would not preserve the required distribution or value statement.

## Exact remaining conditioning and law work

Once padding proves a bound `p_bad ≤ a < 1`, the following are still separate obligations:

1. Define the uniform probability measure on `Fin J → I.RowId`, the good event, and its conditional law. Prove normalization and nonempty support from `p_good ≥ 1-a > 0`.
2. Prove the conditioning inequality used at manuscript lines 1154-1164. For any failure event `F`,

   ```text
   Pr[F | Good] ≤ Pr[F] / (1-a).
   ```

   With `a ≤ 1/4`, this loss is at most `4/3`; the manuscript's factor two is therefore conservative. The proof must keep zero-denominator branches outside conditioning.
3. Prove that conditioning the initial ordered product law on `GoodOrderedQuestion` is uniform over good ordered tuples.
4. Prove the ordered-to-subset pushforward. `GoodOrderedQuestion` includes injectivity and its geometric predicate depends only on `Finset.univ.image u`; every legitimate `J`-element subset should therefore have exactly `J!` orderings. This constant-fibre theorem is what turns the certified ordered law into the manuscript's uniform legitimate-`U` law.
5. Prove the distinct later marginal at manuscript lines 1155-1158: uniform representative or clique resampling inside the declared equivalence classes preserves the uniform legitimate-`U` measure. This needs the actual equivalence relation, equal fibre sizes, equal dimensions, and equal numbers of transverse extensions. It does not follow from the complement bound or from ordinary conditioning.
6. Connect the conditioned question law to honest completeness. The union bound can use the unconditional uniform equation marginals and divide by `Pr[Good]`; it need not assert that each equation coordinate remains uniform after conditioning. The later resampled whole-question marginal nevertheless requires the separate invariance theorem in item 5.
7. Supply an exact finite sampler/enumerator compatible with the eventual `SeededMap` and FP proof. A cardinality identity alone does not give an efficient exact conditional sampler. A rejection sampler is plausible when retained mass is at least `3/4`, but its runtime/seed contract and any bounded-failure repair must be formalized for the headline randomized reduction.

## Claims boundary and remaining headline path

This increment justifies the bounded statement:

> Lean verifies that, for the actual occurrence-row representation with positive row cardinality, a uniform ordered `J`-tuple is a `GoodOrderedQuestion` with rational mass at least `1 - 157 J(J-1)/|RowId|`.

It does not justify saying that the actual constructed source already has high legitimate-question probability, because no row-count/padding inequality has yet been instantiated. It also does not establish source-value preservation, a conditioned or resampled question distribution, actual-star acceptance, the concrete rational formula table, a polynomial-time randomized reduction, hardness, a learning corollary, P versus NP, novelty, or publication readiness.

The direct dependency path is now:

```text
actual_good_ordered_question_uniform_mass_ge  [reviewed here]
  -> source-preserving disjoint-copy constructor and row-count inequality
  -> retained mass at least 1-a, with a <= min(tau/100, 1/4)
  -> conditioned ordered law and failure-loss theorem
  -> uniform pushforward to legitimate J-subsets
  -> equivalence-class/clique-resampling marginal preservation
  -> actual-source question-law instantiation
  -> RHS functional, dimension, transport, and actual-star acceptance
  -> rational table and formula-distribution contract
  -> concrete FP sampler/SeededMap and probability bridge
  -> headline randomized reduction, learning corollary, and manuscript reconciliation.
```

The ledger should accept `actual_good_ordered_question_uniform_mass_ge` as complete with the frozen hashes and three-lens receipts, then make the copy constructor plus value/cardinality preservation the active obligation. The padding task should be rejected if it assumes a new value-preservation field, silently changes the sampled row universe, merges repeated row occurrences, or proves only that the number of rows grows without deriving the quantitative retained-mass target.
