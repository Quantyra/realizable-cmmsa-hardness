# Partition 1 of 9: proof-adversarial review of Full89 A22/HC46 and the selected-consumer path

**Verdict: GO-WITH-NOTES, for this partition only.** This is not a verdict on the whole campaign.

I read every supplied file body in full; none was skipped. I found no defect that blocks the result. I ran nothing and did not look at the source index, as instructed. So the build, axiom and trace claims (seven zero exits, 172 standard axiom profiles, 319-file closure, 7251 nodes, no warnings) are taken as given, not checked. In the supplied text I found no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `unsafe`.

## File coverage (30 of 30 inspected, 0 skipped)

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46A22OriginalInduction | inspected |
| 2 | ActualBinaryMatrixHC46A22ParentFactorization | inspected |
| 3 | ActualBinaryMatrixHC46OriginalExactInhabitant | inspected |
| 4 | ActualSelectedComplementHC46OriginalApplication | inspected |
| 5 | ActualBinaryGrassmannIncidence | inspected |
| 6 | ActualBinaryMatrixHC46 | inspected |
| 7 | ActualBinaryMatrixHC46A11WeightedAggregate | inspected |
| 8 | ActualBinaryMatrixHC46A12FourthMoment | inspected |
| 9 | ActualBinaryMatrixHC46A12InfluenceBound | inspected |
| 10–22 | A17: AdaptedLineDecomposition, CodomainBranch, DerivativeCoordinate, DerivativeGlobalTransfer, DomainBranch, DomainFrequencyCovariance, FixedSlice, Full, GenericParentCoverage, GenericParentEnergy, HomogeneousLineDecomposition, ParentFibreBridge, TransposeHybridFilter | all inspected |
| 23–30 | A18: AmbientHyperplaneLaw, CodomainNormalEnergy, Conditioning, DerivativeRankProjection, EnergyTriangle, FullFunctionalBridge, FullFunctionalEnergy, InductionBounds | all inspected |

Line numbers: without tools I can't count lines reliably, so findings are cited by declaration name.

## Core audit

**`manuscript_A22_actual` (the original A22 theorem)**
- **Quantifiers:** the induction is strong induction on `level`, and inside it the statement holds for all `n' d'`, all `eta : Real` and all `g`. That generality is required, because the lower-level hypothesis is applied to reduced witnesses that live on other spaces (finrank B × finrank of the quotient). `p` stays fixed, which is correct since the hypothesis always uses `pConjugate p`.
- **No circularity:** positive-cost energies are bounded by `B := 2^(500(l-1)²p+6l)·η²` using only the strictly lower level (`ih (level-1)`, with `1 ≤ level` derived from `hpos`).
  - If `E ≤ B`: the proof closes directly.
  - If `E > B`: every influence is at most `E`, since zero-cost energy equals `E` by `a22_zero_cost_energy`. So the premise `OriginalActualInfluenceThrough level E` is actually proved before `a22_dual_energy_of_influences` uses it. The conditional dual estimate is never fed an assumed bound.
- **Level 0:** cost ≤ 0 forces `A=⊥, B=⊤`. The influence premise holds trivially at `E`, and the exponents collapse to 1. Correct.

**`a22_dual_energy_of_influences`**
- **Direction:** the projection pairing is proved exactly, `⟨Pf,f⟩ = ‖Pf‖²` (`a22_projection_pairing`). Hölder then gives `E^p ≤ lpMoment·‖f‖_q^p`, which is the right way round.
- **Moment bound and exponent check:** A21 gives `2^(200j²p²) E (2^(10j²)E)^(m-1)` with `p = 2m`. Then
  `200j²·4m² + 10j²(m-1) ≤ 810 j²m² ≤ 840 j²m² = (420j²p)·m`, which is correct.
- **Cancellation:** cancelling `E^m` needs `E > 0`, and the `E = 0` case is split off first. The final m-th-root step is valid for nonnegative bases.

**`a22_positive_exponent`:** `(j-1)² + j ≤ j²` for `j ≥ 1`, and `6j ≤ 500jp`. Correct. The `420 → 500` relaxation is also correct.

**Parent factorization (`a22_positive_parent_from_lowerIH`)**
- **Case split:** if `A ≠ ⊥`, pick a nonzero `x` and use the line `span{x}`. If `A = ⊥`, positive cost forces `B ≠ ⊤`, so there is a hyperplane `H ⊇ B`.
- **Cost accounting:** both branches charge exactly 1 + (inner cost) via `relative_endpoint_cost_add`, so the inner cost is ≤ `j-1`. The A14 witness constant `2^(3j)` squares to `+6j`, as expected.
- **Mean preservation:** the energy identities (`a22_A1_composition_energy_eq`, `a22_intrinsic_energy_reindex`) are equalities. The various Fintype instances are reconciled through Subsingleton, so normalization is preserved.

**`original_HC46_exact` (eta unrestricted, no hHC premise)**
- **Case `i = 0`:** delegates to `hc46_rank_zero_exact`, which handles `eta > 1` through `‖·‖ ≤ 1 ≤ eta^α`.
- **Case `i ≥ 1`:**
  - Uses `δ = min eta 1`; `eta ≥ 0` is derived from the PR premise. The `δ = 0` case gives `f = 0` and a norm of 0.
  - Density step: `1 + 2a·m = p - 2 + 2/p ≥ p - 2`, and `δ ≤ 1` lets the exponent drop in the right direction.
  - Coefficient: `200i²p² + (10i² + 500i²p)m ≤ 455 i²p² ≤ 500 i²p²`.
  - Final step: `δ^α ≤ eta^α` for `α = (p-2)/p ≥ 0`.

**Selected consumer:** `selected_leaf_HC46_original` passes `original_HC46_exact` into `selected_leaf_HC46_of_exact_PR` and adds no extra premise. The failed-zoom variant derives PR at `2e`.

**A7/A11/A12, A17, A18 support code**
- A10 saving holds: it reduces to `100t² + 10Dk ≤ 110Dt`, given `k ≤ t ≤ D`.
- The i/j tails hold for `D ≥ 1`: `4r ≤ 2^(-31D)`, and `2·2^(-67Dk) ≤ 2^(-31D(k+1)-4Dk)`.
- A12: the selected-pair count is at most `2^(2·rank²) ≤ 2^(3D²)`, so the exponent is `103 = 100 + 3`, and A19 is `114 = 103 + 11`.
- A18 absorption constants check out: `1/512 + 1/64 = 9/512`, and `1/2 + 2/961 ≤ 1`.

## Findings

| ID | Severity | Declaration | Finding |
|---|---|---|---|
| F1 | Low | `ParentFactorization.a22_parent_from_order_one_coordinate` | This is a conditional lemma: `hderived` is a premise. Its docstring says it is "applied only after the A14 witness and strict lower-level induction". It isn't called anywhere in the supplied files; the main chain goes through the line/hyperplane `*_from_lowerIH` theorems instead. It must not be cited as an unconditional fact, and the docstring should be fixed. |
| F2 | Info | `A17ParentFibreBridge` module header | The comment is stale. It says that identifying the map with the matrix lift is "a separate obligation", but `carrierAmbientLiftFibreEquiv_apply` and `liftCarrierMatrix_normalizedMean` prove exactly that in the same file. |
| F3 | Info | `A17DomainFrequencyCovariance.complexAmbientHybridFilter_eq_homFilter_aux`; A11 file header | These use `set_option diagnostics true` with `maxHeartbeats 800000`, and A11 sets `backward.isDefEq.respectTransparency false`. `with_unfolding_all` also appears in DerivativeGlobalTransfer and ParentFibreBridge. All of these affect the elaborator only, since the kernel re-checks everything, so there is no soundness impact. Diagnostics may emit info messages, though, so this needs reconciling with the "no warnings" claim at the log level. |
| F4 | Info | A11 module header | The header says "accepted with notes at frozen run 56". That is a provenance claim in a comment, not evidence; I gave it no weight. |
| F5 | Info | `actual_A17_*_branch` (`hDpos`); `original_HC46_exact` (`hEven` when `i ≥ 1`); GrassmannIncidence `pointed_bottom_relation_iff` / `pointed_fibre_equiv` (`{r}`) | These hypotheses or binders are unused. That only makes the theorems stronger than stated, so it isn't a proof defect. I can't confirm from text alone whether the linter flags them. |

## Open questions for integration (not answerable from this partition)

1. **Contract and definitions:** the statements of `HC46ExactContract`, `PseudorandomExact`, `UpToActualLqGlobal` (plus `_whole`, `_parameter_nonneg`, `_raw_typed`), `UpToCarrierLqGlobal`, `OriginalActualInfluenceThrough`, `pConjugate`, `realQNorm`, `lpMoment` and `lpNorm`.
   - In particular: does `exactPR_to_actual_LqGlobal` produce parameter `(min eta 1)^(1-1/p)` at level `r`? The `hLqi` ascription assumes it does.
2. **Analytic engines used here:** `manuscript_A21_actual`, `actual_A18_original_global`, `realQNorm_holder_nat_pow`, `a22_typed_*_witness_global`, `a22_A14_coefficient_le`, `typed_A14_fixedLine` / `typed_A14_fixedHyperplane`, `original_influence_A1_relative_mean`, `manuscript_A1_complex`, `a7_zero_order_component`, `a7_positive_of_mixed_bound`, `manuscript_A7_degree_zero`, the A8/A9 charge lemmas, `typedW6AllPairs_uniformT_le_two`, `filteredCarrierFunction_energy_le_A16`, `actual_fixed_functional_line_average_energy_le_two`, and the transpose-restriction lemmas.
3. **Whether the consumer's premises can be satisfied:** `selected_leaf_HC46_of_exact_PR` and `selected_leaf_failed_zoom_PR` (including whether `hfail` can be met), `boolean_mean_le_of_exact`, and `complexRankProjection_boolean_eq`.
4. **External boundary:** the pinned Init/Mathlib/Batteries trust is accepted as stated and not reviewed here.
5. **Still-open gates, untouched by this review:** Spectral47; source/star/robust8S/numericNO/encoded reduction; runtime/learning; upstream bridges; and manuscript/render/novelty. That includes whether the constants `500j²p`, `420`, `103`, `114` match the manuscript.
