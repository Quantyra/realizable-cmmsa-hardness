# Complexity review, partition 8 of 9: A1, A14/A15 typed carriers, and matrix-lift/Grassmann substrate

**Verdict: GO-WITH-NOTES.** This verdict covers partition 8 only. It is not a verdict on the whole campaign.

**What I did:** I read every file supplied in this message, from source text only. I used no tools: I did not compile, run code, read files, or open the source index. I could not check the stated SHA256 values, and I could not map this partition's declarations onto the 172-root theorem list.

**Main limits:**
- The HC46 and A22 statements themselves (unrestricted-eta HC46, real-q A22) are **not in this partition**. I checked only the lemmas that feed them.
- No hypothesis named `hHC`, and nothing that works like one, appears in any of the 45 files.
- Whether the shared consumer adds such a premise can only be settled during integration.

## 1. File inventory: 45 complete files, all inspected, none skipped

| # | File | Status |
|---|---|---|
| 1 | BinaryMatrixA1Complex | inspected |
| 2 | BinaryMatrixA1Composition | inspected |
| 3 | BinaryMatrixA1NestedCarrier | inspected |
| 4 | BinaryMatrixA1Phase | inspected |
| 5 | BinaryMatrixA1TypedFourier | inspected |
| 6 | BinaryMatrixActualAffine | inspected |
| 7 | BinaryMatrixActualAffineCarrier | inspected |
| 8 | BinaryMatrixCodomainA14 | inspected |
| 9 | BinaryMatrixCodomainA15 | inspected |
| 10 | BinaryMatrixComplexA14 | inspected |
| 11 | BinaryMatrixComplexA15 | inspected |
| 12 | BinaryMatrixFirstDerivative | inspected |
| 13 | BinaryMatrixFourier | inspected |
| 14 | BinaryMatrixHybridSelector | inspected |
| 15 | BinaryMatrixLineA14 | inspected |
| 16 | BinaryMatrixLineA15 | inspected |
| 17 | BinaryMatrixLineTranslation | inspected |
| 18 | BinaryMatrixNestedSelectorA1 | inspected |
| 19 | BinaryMatrixTypedA14FixedBase | inspected |
| 20 | BinaryMatrixTypedA14Hyperplane | inspected |
| 21 | BinaryMatrixTypedA14HyperplaneFixedBase | inspected |
| 22 | BinaryMatrixTypedA14HyperplaneReduced | inspected |
| 23 | BinaryMatrixTypedA14Line | inspected |
| 24 | BinaryMatrixTypedA14Reduced | inspected |
| 25 | BinaryMatrixTypedA15AdaptedGlobal | inspected |
| 26 | BinaryMatrixTypedA15Hyperplane | inspected |
| 27 | BinaryMatrixTypedA15HyperplaneGlobal | inspected |
| 28 | BinaryMatrixTypedA15HyperplaneReduced | inspected |
| 29 | BinaryMatrixTypedA15HyperplaneReducedGlobal | inspected |
| 30 | BinaryMatrixTypedA15OneStep | inspected |
| 31 | BinaryMatrixTypedA15Reduced | inspected |
| 32 | BinaryMatrixTypedA15ReducedGlobal | inspected |
| 33 | BinaryMatrixTypedA15Transport | inspected |
| 34 | BinaryMatrixTypedHyperplaneIntrinsicP | inspected |
| 35 | BinaryMatrixTypedHyperplaneSelector | inspected |
| 36 | GrassmannCounting | inspected |
| 37 | GrassmannFlagPosterior | inspected |
| 38 | MatrixFullRowRankHalf | inspected |
| 39 | MatrixGrassmannFibre | inspected |
| 40 | MatrixGrassmannIncidence | inspected |
| 41 | MatrixGrassmannIntersectingAnchor | inspected |
| 42 | MatrixGrassmannMoment | inspected |
| 43 | MatrixLiftAffineTarget | inspected |
| 44 | MatrixLiftExactBudgetZoom | inspected |
| 45 | MatrixLiftFullRowRankBridge | inspected |

Several files import modules that were not supplied: `BinaryMatrixA1CoefficientTransfer`, `BinaryMatrixA1CharacterBridge`, `GrassmannIncidence`, `TripleRestrictionRank`, `VectorAdvice` and `PosteriorReweighting`. These belong to other partitions; section 5 lists what integration must confirm about them.

## 2. Core mathematical checks: these all held

**Multiplier formula (`lineTranslationMultiplier_eq_hybrid`).** The averaging operator E multiplies the character χ_Y by 0 if Y is selected and by 2^(−rank Y) if it is not.
- The count is exact. When Y is unselected, the number of φ with Y·snoc(φ,1)=0 equals |ker(drop Y)| = 2^(d−rank). The required rank equality comes from `rank_eq_drop_add_hybrid_indicator`.
- When Y is selected, `lineFrequency_ne_zero_of_hybridLineSelected` rules out φ with Y·snoc(φ,1)=0, so the multiplier is 0.

**A14 (`rankProjection_rawRestrict_lineP_eq_hybridDerivative`).** The proof goes character by character.
- When the induced rank is j, the input rank must be j or j+1. On those two ranks, `lineP_scalar_at_adjacent_rank` reduces the polynomial's scalar to [selected].
- Several input frequencies can induce the same reduced frequency. Those collisions are handled by linearity (`rankProjection_finset_sum`); no assumption that they are disjoint appears.
- Index convention: Lean's `lineP j` is the manuscript's P_{j+1} = (I−2^{j+1}E)(I−2^jE). It has input rank j+1 and output rank j. The docstring states this convention, and the code follows it consistently.

**A15 constant (`upToRawSquareGlobal_lineP`, `complexLineP_raw`).**
- Each factor costs (x−ay)² ≤ 2x² + 2a²y², and averaging does not increase the bound.
- Writing a=2^j and b=2a gives (1+a²)(1+b²) ≤ 4a²b² = b⁴, so the total factor is 4·b⁴ = 4·2^{4(j+1)}. The constant is correct and is never stated in the reverse direction.
- Restricting to a fixed base costs exactly one equation (`liftRestriction_budget = budget+1`). That justifies the premise at level k+1 and the conclusion at level k.

**Raw versus actual restrictions.** The two forms are proved equivalent in both directions:
- `upToActual_implies_upToRaw` needs ε ≥ 0, because an empty raw fibre gives 0/0 = 0.
- `upToRaw_implies_upToActual` needs no extra hypothesis.
- The transfers to and from typed, line-coordinate, hyperplane-coordinate and reduced-coordinate forms are all genuine `↔` statements. No direction is lost.

**A1 composition (`derivative_composition_A1` → `manuscript_A1_restrict_filter` → `manuscript_A1_complex`).**
- `selected_nested_iff` is proved in both directions, with no complement or dimension assumption.
- The phase law comes from cyclicity of the trace.
- The affine base law and the nested carrier equivalence are canonical: no basis is chosen.

**Selectors are intrinsic.**
- `typedLineSelected`: the line generator lies in range Y. Over F₂ the generator is unique, so this is canonical.
- `typedHyperplaneSelected_iff_ker_le`: the hyperplane selector is equivalent to ker Y ≤ H.
- `intrinsicHyperplaneP_eq_typed`: the intrinsic hyperplane polynomial equals the coordinate (basis-dependent) version.

**Matrix lift.**
- `card_homFibre` shows each fibre has the same size, ∏(2^{z+k} − 2^{z+i}), even when the anchor meets H.
- Rank-deficient matrices score exactly zero; nothing is resampled.
- The factor 2 needs nonnegative scores (`hg`), which the theorem assumes.
- `full_row_rank_gt_half` is correct: with c < k, 2^{c+1} − 2 < 2^k. The edge case c = 0 also holds.

**Exact-budget refinement (`smaller_budget_zoom_density_le`, `smaller_budget_of_exact_r`).**
- The flag double count is exact. The empty refined zooms that the `Nonempty` guard excludes contribute zero.
- The natural-number subtraction is safe: from `hbudget`, a + (n−w) = r and q ≤ a ≤ d hold.

## 3. Conditional facts versus universal claims

None of the following should be reported as unconditional:

- **All globalness transfers:** need `0 ≤ ε`.
- **Typed line and hyperplane results:** need `finrank L = 1` or `finrank (B⧸H) = 1`. They are vacuous when no such L or H exists, which is correct behaviour.
- **`homogeneous_lift_density_le`:** takes the zoom bound `hzoom` as a hypothesis. That bound is discharged only through `homogeneous_lift_density_of_exact_r`, which needs `ExactBudgetZoomBound r (q+k)`, `r < q+k`, a budget bound, and `W = Q ⊔ H`.
- **`affine_target_*`:** take `hhalf` as a hypothesis. The bridge discharges it, but only for C = Fin c → F₂ with **c < k**.
- **Bridge definitions:** take the surjectivity premise `hX₁` and an arbitrary H.
  - `residual_row_surjective` would derive `hX₁` when H = ker X₀.
  - Nothing ties H to ker X₀ inside the bridge, so the consumer must do this.
- **GrassmannFlagPosterior:**
  - `containmentProbability_formula` and `eventMarginal_formula` need a ≤ d ≤ J.
  - `eventPosterior_eq_conditional` additionally needs `hpos`.
  - On a null event the posterior is algebraically 0, not a conditional law, as the docstring says.
- **`binary_hc_rankZero*` and `binary_hc_rankLevel_L2_exact`:** cover the rank-0 slice and the rank-level L² bound only. They are not the hypercontractive inequality.

## 4. Findings

No Critical or High findings.

**F1 — Medium (integration risk): `PseudorandomExact` pads with zero equations.**
- Where: `BinaryMatrixFourier`, `exactWholeRestriction` / `boolean_mean_le_of_exact`.
- The raw "nominal budget exactly r" premise is met by r zero rows, so it is equivalent to "budget ≤ r" and contains the whole space.
- That is sound as a hypothesis. But a manuscript premise stated over *actual* order-exactly-r restrictions does not directly give this raw form; getting there needs an averaging bridge, like the one `MatrixLiftExactBudgetZoom` provides for zooms.
- Action: integration must confirm that no HC46/A22 consumer takes `PseudorandomExact` as the manuscript premise without that bridge. If none does, this drops to Info.

**F2 — Low: stale "UNCOMPILED" headers contradict the build evidence.**
- Affected files: `GrassmannCounting` (line 1, "No Lean4.34 verification…"), `GrassmannFlagPosterior` (line 1), `MatrixGrassmannIncidence`, `MatrixGrassmannMoment` and `MatrixGrassmannFibre` (module docstrings).
- `MatrixLiftExactBudgetZoom` and `MatrixLiftFullRowRankBridge` import these modules, so they must be in the compiled closure.
- Action: integration should confirm they are among the 319 source-closure files, then remove the headers before the manuscript/render gate.

**F3 — Low: `GrassmannCounting` and `GrassmannFlagPosterior` leave auto-implicit variables on.**
- These are the only supplied files that do not set `set_option autoImplicit false`.
- Variables such as `a`, `d`, `n` and `J` are bound implicitly. The build is clean, but this is weaker hygiene than the rest of the partition.

**F4 — Info: `BinaryMatrixTypedA15Hyperplane` closes only its innermost namespace.**
- It ends with `end BinaryMatrixTypedA15Hyperplane`, so `PvNP.RealizableHardness` stays open at end of file.
- Lean 4 accepts this, so it causes no build error. It is inconsistent with the other files.

**F5 — Info: duplicate `columnLinear` definitions.**
- `MatrixFullRowRankHalf.columnLinear` and `MatrixLiftAffineTarget.columnLinear` are textually identical.
- `binary_target_half` relies on them unfolding to each other definitionally.
- The bridge results are `def`s whose types are propositions (`linter.defProp` is turned off). Axiom profiles are unaffected.

**F6 — Info: non-default elaboration settings.**
- `backward.isDefEq.respectTransparency false` is set in `MatrixGrassmannFibre` and `MatrixGrassmannIncidence`.
- `maxHeartbeats` is raised to 600k–800k in several typed A14/A15 files.
- These affect elaboration only; the kernel still checks every proof.

**F7 — Info: unused parameters.**
- `hyperplaneReducedFrequencyEquiv` and its lemmas take B and hH without using them.
- `_hdyadic`, `_hδ₀` and `_hδ₁` are explicitly unused.
- None of these makes a statement vacuous.

**F8 — Info: the intrinsic hyperplane polynomial is proved for one functional only.**
- `intrinsicHyperplaneP_eq_typed` is stated for `hyperplaneDefiningFunctional`, not for an arbitrary ψ with ker ψ = H.
- Over F₂ any such ψ equals that functional, but that uniqueness lemma does not appear here.
- Action: if the consumer quantifies over arbitrary ψ, integration needs the lemma.

## 5. Questions left open for integration

1. **`BinaryMatrixA1CoefficientTransfer`:**
   - `nextDerivative_eq_restrict_hybridFilter` is proved by `rfl`, so `nextDerivative` must literally be `carrierAffineRestrict ∘ carrierHybridFilter`.
   - Confirm also `initialDerivative` and `initialDerivative_fourierCoeff`.
2. **`BinaryMatrixA1CharacterBridge`:** confirm the transpose convention in `traceCharacter_eq_matrix_character` and `tracePair_matrix`. The ambient frequency used is `Y.transpose.toLin'`.
3. **`GrassmannIncidence` and the `TripleRestrictionRank`/`VectorAdvice`/`PosteriorReweighting` group:** confirm `incidenceCount_pos` (including its dimension precondition on `retained`), `kernel`, `prior`, `conditional` and `adviceMarginal`.
4. **HC46/A22 consumer (other partitions):** confirm that it:
   - uses the Actual/Typed globalness forms,
   - discharges `ExactBudgetZoomBound` / `hzoom`, `hX₁`, H = ker X₀ and c < k from manuscript premises rather than assuming them,
   - does not route through `PseudorandomExact` (F1),
   - introduces no `hHC` premise.
5. **Mapping to the 172 roots:** match these 45 files' declarations against the 172-root theorem list.
6. **External boundary (explicit library trust, not newly reviewed):** the Mathlib lemmas relied on include `card_linearIndependent`, `Matrix.card_GL_field`, `LinearMap.trace_comp_comm'`, `LinearMap.trace_conj'`, `Module.Projective.exists_dual_eq_one`, `LinearMap.range_dualMap_eq_dualAnnihilator_ker`, `Submodule.quotientQuotientEquivQuotient`, `finrank_span_eq_card`, `Real.self_le_rpow_of_le_one` and `sum_div_card_sq_le_sum_sq_div_card`.

Still open outside this partition: the broader Spectral47 work; the source/star/robust8S/numericNO/encoded-reduction/runtime/learning gates; upstream bridges; and the manuscript, render and novelty gates.
