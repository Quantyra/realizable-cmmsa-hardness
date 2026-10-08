# Partition 1/9 review: Full89 original A22 / HC46 / selected-consumer milestone

**Verdict: GO-WITH-NOTES.** This covers only this partition. It is not a verdict on the whole campaign. I found no blocking issue in the 30 files supplied here. All 30 bodies were inspected and none were skipped. Several dependencies sit outside this partition and are listed below for integration.

**Basis of the review.** I read the sources by hand. I ran no Lean/Lake and no code, and I did not open the source index. I treated the reported build results (seven zero exits, 172 axiom profiles, the trace with zero unresolved nodes) as context you supplied. I did not reproduce them, so they are inherited claims, not something I checked. Findings cite declarations by name; I did not count line numbers, so none are given.

## Files inspected (30 of 30, none skipped)

1. ActualBinaryMatrixHC46A22OriginalInduction.lean
2. ActualBinaryMatrixHC46A22ParentFactorization.lean
3. ActualBinaryMatrixHC46OriginalExactInhabitant.lean
4. ActualSelectedComplementHC46OriginalApplication.lean
5. ActualBinaryGrassmannIncidence.lean
6. ActualBinaryMatrixHC46.lean
7. ActualBinaryMatrixHC46A11WeightedAggregate.lean
8. ActualBinaryMatrixHC46A12FourthMoment.lean
9. ActualBinaryMatrixHC46A12InfluenceBound.lean
10. A17AdaptedLineDecomposition
11. A17CodomainBranch
12. A17DerivativeCoordinate
13. A17DerivativeGlobalTransfer
14. A17DomainBranch
15. A17DomainFrequencyCovariance
16. A17FixedSlice
17. A17Full
18. A17GenericParentCoverage
19. A17GenericParentEnergy
20. A17HomogeneousLineDecomposition
21. A17ParentFibreBridge
22. A17TransposeHybridFilter
23. A18AmbientHyperplaneLaw
24. A18CodomainNormalEnergy
25. A18Conditioning
26. A18DerivativeRankProjection
27. A18EnergyTriangle
28. A18FullFunctionalBridge
29. A18FullFunctionalEnergy
30. A18InductionBounds

## Core audit

**A22: `manuscript_A22_actual`**
- **Conditional.** It assumes `UpToActualLqGlobal j (pConjugate p) eps f`, `p ≥ 2` and `p` dyadic. From these it concludes `OriginalActualInfluenceThrough j (2^(500 j² p)·eps²) (complexRankProjection j f)`.
- **Induction.** Strong induction on the level, quantified over every finite space (`n' d' eta g`).
- **Positive-cost carriers.** These use only `ih (level-1)`, through `a22_positive_parent_from_lowerIH`.
- **Zero-cost carriers.** These reduce exactly to the energy E (`a22_zero_cost_energy`).
- **No circularity.** The duality estimate `a22_dual_energy_of_influences` is applied only after one of two things is established. Either E ≤ B already closes the case, or E > B, in which case every influence is shown to be ≤ E (`hclose E le_rfl …`). Level 0 is handled separately and needs only the zero-cost bound.
- **Proof direction is correct.**
  - The pairing equals E (`a22_projection_pairing`, a genuine orthogonality identity).
  - Hölder then gives Eᵖ ≤ moment·epsᵖ.
  - A21 gives moment ≤ C·Eᵐ with p = 2m.
  - Cancelling Eᵐ when E > 0 gives E ≤ 2^(420 j² p)·eps².

**HC46 contract: `original_HC46_exact`**
- **Universal** over the contract, with no `hHC` premise.
- **Arbitrary eta.**
  - eta ≥ 0 is derived from `hPR`.
  - delta = min(eta, 1).
  - The case delta = 0 forces f = 0.
  - The final step uses the monotonicity of rpow with exponent (p−2)/p ≥ 0, so eta > 1 is handled.
- **Rank 0** is delegated to `hc46_rank_zero_exact`. Its eta > 1 branch uses ‖proj₀‖ₚ = mean ≤ 1 ≤ eta^α.
- **The q-norm parameter direction is correct:** delta^(1−1/p) = delta^(1/q).

**Selected consumer: `selected_leaf_HC46_original`**
- It passes `original_HC46_exact` in as the contract argument, so the contract is discharged rather than left as a caller hypothesis.
- `selected_leaf_failed_zoom_HC46_original` is **conditional** on `hfail` (with eta = 2e, e ≥ 0).

**A7/A12/A19 and A17/A18**
- `manuscript_A7_actual` uses strong induction with only the strict lower-degree hypothesis.
- `manuscript_A12_actual` and `manuscript_A19_actual` are conditional on influence/globalness.
- `actual_A17_full_parent_energy` is conditional on source globalness, on derivative globalness of every order-one derivative, and on homogeneity.
- The A18 bounds are all conditional.

### Numerical exponent checks (all verified by hand)

| Location | Inequality | Status |
|---|---|---|
| `a22_dual_energy_of_influences` `hexp` | 200j²p² + 10j²(m−1) ≤ 810j²m² ≤ 420j²p·m, with p = 2m | ✓ |
| `a22_positive_exponent` | 500(j−1)²p + 6j ≤ 500j²p for j ≥ 1, using (j−1)² + j = j² − j + 1 | ✓ |
| witness rescaling (line/hyperplane) | 2^(500(j−1)²p)·(2^(3j)·eps)² = 2^(500(j−1)²p + 6j)·eps² | ✓ |
| `original_HC46_moment_density_algebra` | 200i²p² + (10i² + 500i²p)·m ≤ 455i²p² ≤ 500i²p², with 2m ≤ p | ✓ |
| density exponent | 1 + 2(1−1/p)(p/2−1) = p − 2 + 2/p ≥ p − 2, and delta ≤ 1 so a larger exponent gives a smaller value | ✓ |
| `a11_full_A10_exponent_saving` | 100t² + 10Dk ≤ 110Dt, from t ≤ D and k ≤ t | ✓ |
| `a11_full_finite_ij_tail` | k = 0: 4·2^(−63D) ≤ 2^(−31D); k ≥ 1: 1 + 31D ≤ 32Dk | ✓ |
| `a12_selected_mass_bound` | 2r² ≤ 3D² for r ≤ D | ✓ |
| `a18_top_contribution_le_nine512`, `a18_lower_absorption` | 1/512 + 1/64 = 9/512; 1/2 + 2/961 ≤ 1 | ✓ |

## Findings (none blocking)

1. **LOW, hygiene: some files depend on auto-bound implicits.**
   - `A18Conditioning.dualSupVectorCoordinate_card` uses a type `W` that is never declared in a `variable` line, so it is auto-bound.
   - These files lack `set_option autoImplicit false`: A17HomogeneousLineDecomposition, A18AmbientHyperplaneLaw, A18CodomainNormalEnergy, A18Conditioning, A18EnergyTriangle, A18FullFunctionalBridge, A18FullFunctionalEnergy and A18InductionBounds.
   - Scanning those files, I found no other auto-bound name. The auto-bound `W` makes that statement more general, not weaker.

2. **LOW, hygiene: leftover debugging options.** `A17DomainFrequencyCovariance.complexAmbientHybridFilter_eq_homFilter_aux` carries `set_option diagnostics true in` and `maxHeartbeats 800000`. These produce diagnostic info output in the build log, not warnings, and do not affect soundness.

3. **LOW, documentation: stale or overclaiming docstrings.**
   - The A11 module docstring says it was "accepted with notes at frozen run 56 … separate reviews". That is an acceptance claim written into the source. It is not evidence, and this review does not rely on it.
   - The `a11_weighted_actual_mixed_le_final_sum` docstring still says the A9 aggregate is "forthcoming".
   - The `hc46_rank_zero_exact` docstring says "positive-rank estimate is the remaining HC46 engine step". That is now superseded by `original_HC46_exact`.
   - The A17ParentFibreBridge module docstring calls the matrix-lift identification "a separate theorem obligation", but `carrierAmbientLiftFibreEquiv_apply` in the same file proves it.

4. **INFO: unused premises or arguments (none weakens a conclusion).**
   - `hEven` is unused in HC46: the bound is proved without d = 2h.
   - `hDpos` is unused in the A17 branches.
   - The `T` argument of `carrierAmbientQuotientHomEquiv` is unused.
   - `pointed_bottom_relation_iff` and `pointed_fibre_equiv` carry an unused implicit `{r}`. In `pointed_fibre_equiv` it cannot be inferred, so a caller must write `(r := _)`.
   - `pointedQuery_empty_of_not_le` takes an unused `C`.

5. **INFO: a conditional lemma off the main path.** `a22_parent_from_order_one_coordinate` takes `hderived` as a premise. It is not used on the path to `manuscript_A22_actual` in this partition; positive parents go through the line/hyperplane `_from_lowerIH` lemmas instead.

6. **INFO: GrassmannIncidence gates.**
   - `GenericUpTo W 0 r` is vacuous by design, and the docstring says so.
   - The truncated-subtraction gates in `bottomRegularIncidence` and `pointedRegularIncidence` correctly imply positivity of `fibreCard`.

## Open for integration (cross-partition and external boundaries)

**Definitions not supplied here.** The exact text of each needs checking, for vacuity and quantifier shape:
- `HC46ExactContract`. It must be the unchanged contract. I inferred its shape from the `intro` and the final goal only.
- `PseudorandomExact`, `AffineRestriction.budget`
- `UpToActualLqGlobal`, `UpToCarrierLqGlobal`, `UpToActualNormSqGlobal`
- `OriginalActualInfluenceThrough`, `Selected`
- `realQNorm`, `pConjugate`, `lpMoment`, `lpNorm`
- `a7HybridQ`, `typedW6QComponent`

**Lemmas consumed without their bodies being here:**
- A18/A21: `actual_A18_original_global`, `manuscript_A21_actual`, `actual_fixed_functional_line_average_energy_le_two`.
- Hölder and globalness projections: `realQNorm_holder_nat_pow`, `UpToActualLqGlobal_whole`, `UpToActualLqGlobal_parameter_nonneg`, `UpToActualLqGlobal_raw_typed`.
- A14 witnesses and coordinates: `a22_typed_line_witness_global`, `a22_typed_hyperplane_witness_global`, `a22_A14_coefficient_le`, `typed_A14_fixedLine`, `typed_A14_fixedHyperplane`, `reducedRankProjection_coordinate`, `hyperplaneReducedRankProjection_coordinate`.
- A1 and relative-cost structure: `original_influence_A1_relative_mean`, `relative_endpoint_cost_add`, `manuscript_A1_complex`.
- Boolean/PR inputs: `exactPR_to_actual_LqGlobal` (its conclusion must be stated in terms of `min eta 1`), `boolean_mean_le_of_exact`, `binary_hc_rankZero_exact`, `complexRankProjection_boolean_eq`.
- Selected-leaf consumer: `selected_leaf_HC46_of_exact_PR`, `selected_leaf_failed_zoom_PR`.
- A7–A16 inputs: `a7_positive_of_mixed_bound`, `manuscript_A7_degree_zero`, the a8/a9 partition and charge lemmas, `typedW6AllPairs_uniformT_le_two`, `filteredCarrierFunction_energy_le_A16`.
- Transpose and Spectral47-related transport lemmas.

**Non-vacuity of `hPR`.** Padding (`padRestrictionToBudget`) shows that exact-budget-r restrictions exist once there is a base restriction of budget ≤ r with a nonempty fibre. Whether such a base exists depends on the `AffineRestriction` definition and on `boolean_mean_le_of_exact`, both outside this partition.

**Library trust.** Init, Mathlib and Batteries are trusted as pinned library sources. They were not reviewed here as new proof.

**Gates that remain open.** Spectral47; source/star/robust8S/numericNO/encoded reduction/runtime/learning; upstream bridges; manuscript, render and novelty gates. This review gives no acceptance on any of them.
