# Partition 7/9 review: Full89 A22 / HC46 / selected-consumer complexity

## Verdict: GO-WITH-NOTES (this partition only; not a whole-campaign verdict)

I inspected all 35 supplied complete files and skipped none. I found no defect inside the partition that blocks it. Two things limit what it shows:

- The selected material consumer here is still conditional on two premises: `hHC : HC46ExactContract` and `hSpectral : Spectral47ExactContract`.
- The milestone claim that the consumer has "no added hHC premise" can't be confirmed from this partition. Only the `…HC46OriginalApplicationChecks` file is here, not the application file it checks.

**How I reviewed it:**
- I read the files as text only. I didn't run Lean or Lake, read the source index, or verify the SHA256 values.
- For elaboration I relied on the stated zero-error, zero-warning GCP build. I checked the logic, direction, quantifiers and arithmetic myself.
- References below are by declaration name. I didn't count line numbers by hand, because without tools they would be unreliable.

## File inventory (all inspected)

1. ActualSelectedComplementAnalyticMoment.lean
2. ActualSelectedComplementAppendMoment.lean
3. ActualSelectedComplementHC46OriginalApplicationChecks.lean (only `#check` / `#print axioms`; its output wasn't supplied)
4. ActualSourceStarLaw.lean
5. ActualTaggedConditionalGraphCount.lean
6. ActualTypedABArbitraryRankProjection.lean
7. ActualTypedABBottomTopRankReindex.lean
8. ActualTypedABCanonicalDCollapse.lean
9. ActualTypedABCanonicalEndpointCollapse.lean
10. ActualTypedABCanonicalFlag.lean
11. ActualTypedABCanonicalProjection.lean
12. ActualTypedABCanonicalRankProjectionCollapse.lean
13. ActualTypedABCanonicalRankProjectionEnergy.lean
14. ActualTypedABCanonicalSignalCollapse.lean
15. ActualTypedABEndpointTransport.lean
16. ActualTypedABFullA16Assembly.lean
17. ActualTypedABFullA16Final.lean
18. ActualTypedABHybridSelectorSteps.lean
19. ActualTypedABMixedTower.lean
20. ActualTypedABOriginalGlobalBridgeClean.lean
21. ActualTypedABProjectionEnergy.lean
22. ActualTypedABRankedTower.lean
23. ActualTypedCarrierAmbientBudget.lean
24. ActualTypedFourierEquivNaturality.lean
25. ActualTypedIntrinsicHyperplaneNaturality.lean
26. ActualTypedIntrinsicWitnessNaturality.lean
27. BinaryMatrixA15A1Carrier.lean
28. BinaryMatrixA15BaseCase.lean
29. BinaryMatrixA15CanonicalLineRank.lean
30. BinaryMatrixA15CanonicalRank.lean
31. BinaryMatrixA15NestedHyperplane.lean
32. BinaryMatrixA15NestedLine.lean
33. BinaryMatrixA15SelectedBridge.lean
34. BinaryMatrixA1CharacterBridge.lean
35. BinaryMatrixA1CoefficientTransfer.lean

I saw no `sorry`, `axiom`, `native_decide` or `opaque` in any supplied file.

## Findings

**F1: the hHC premise is still present in this partition's selected consumer.** Severity: high for the milestone claim, none for soundness. Integration item.

- Where it appears in `ActualSelectedComplementAnalyticMoment`:
  - `selected_actual_material_moment_bound` and `selected_actual_HC_spectral_moment_bound` both take `hHC : HC46ExactContract`.
  - So do `selected_low_append_HC46_lpNorm_bound`, `selected_leaf_append_level_HC46` and `selected_leaf_HC46_of_exact_PR`.
- `HC46ExactContract` is universal: it ranges over every `b : BinaryMatrix n d → Bool` and every real `eta`.
- The consumer only ever applies it to one function, `b = selectedF T f`, inside `selected_low_append_HC46_lpNorm_bound`.
- **Question for integration:** the referenced `selected_leaf_HC46_original` and `selected_leaf_failed_zoom_HC46_original` must either prove the full universal contract, or the "no hHC" consumer must be a separate theorem that re-derives the chain. Judging by its name, a selected-leaf-only theorem could not be passed as `hHC` to `selected_actual_material_moment_bound` as that theorem is stated. This needs confirming in the partition that holds `ActualSelectedComplementHC46OriginalApplication.lean`, along with its `#print axioms` output.

**F2: the material bound depends on Spectral47.** Severity: informational; Spectral47 is already open per scope.

- `selected_leaf_high_energy_le_spectral` and everything downstream take `hSpectral : Spectral47ExactContract sourceHeightCutoff`, with `sourceHeightCutoff` quantified over all choices.
- So `selected_actual_material_moment_bound` is a conditional result, not a universal one.
- This review doesn't assess whether the contract is true. Its stated form:
  - quantifies every real `F` that is invariant under right multiplication by invertible matrices (`basisInv`);
  - has no `c+s ≤ n` guard and no `rho < 1` guard (`hc` implicitly forces `rho ≤ 1`);
  - uses the bound `2^{-i(s-1)} + 3·2^{i-n}`, which reduces to the trivial Bessel bound at `i = 0`.

**F3: eta is unrestricted in the HC46 contract.** Severity: low; vacuity depends on a definition in another partition.

- `HC46ExactContract` has no `0 ≤ eta` or `eta ≤ 1` premise, as its docstring says.
- For `eta < 0`, `Real.rpow` gives `exp(log|eta|·y)·cos(πy)`. At `p = 4` that is exactly 0, so the contract would force `lpNorm = 0`.
- Whether the contract can be true for all eta therefore depends on whether `PseudorandomExact r eta b` can hold with `eta < 0`. If it is a density bound over restrictions that include the whole space, it can't, and the contract is fine. That definition must be checked where `PseudorandomExact` is defined.
- The consumer only ever uses `eta = 2·(e : ℝ)` with `e ≥ 0`, via `selected_leaf_failed_zoom_PR` and `actual_leaf_failed_zoom_gives_nominal_pseudorandom`.

**F4: exact budget versus all levels below it.** Severity: informational; integration item.

- `hfail` in `selected_actual_material_moment_bound` only constrains zooms with `q + codim P.W = r` exactly.
- The HC46 contract then consumes `PseudorandomExact r` for every level `i ≤ r`.
- Integration needs to confirm that the original HC46 proof only needs the exact-`r` budget, or that `PseudorandomExact` is monotone in its order. Otherwise the original theorem's hypotheses don't match the source's HC4.6.

**F5: numerical exponents and direction.** Severity: informational, for parameter and manuscript gates.

- Direction is correct throughout, and everything is an upper bound:
  - `matchingStarMass ≤ 2·selectedActualMoment`, using the rank-loss bound ≤ 1/2 in `rankloss_from_exponent`;
  - the selected center mean ≤ the Grassmann beta, because `alpha ≤ 1` in `selected_center_matrix_mean_le_exact_grassmann_beta`;
  - Hölder (`selected_low_weighted_holder`) with `p/m ≥ 1`, then dropping the weight because the indicator is ≤ 1.
- Exponent window: `exists_dyadic_moment_exponent_window` gives `4m ≤ k < 8m` with `k` a power of 2, and requires `m > 0` (in Hölder, `m = 0` makes `hp` false).
- Beta exponent: `1 − m/k ≥ 3/4`.
- The low term is at most `2^m · beta^{1−m/k} · ((r+1)·2^{500 r² k} · eta^{(k−2)/k})^m`.
  - Here `500·r²·k·m < 4000·r²·m²`.
  - The eta exponent `m(k−2)/k` is at least `m − 1/2`.
  - So the low term is only non-trivial when eta is about `2^{−Θ(r² m)}` or smaller.
  - The low index set includes level 0.
- Other arithmetic I checked:
  - `selected_rankloss_exponent`: `2h(m+2) ≤ 2h²` follows from `m + 2 ≤ h`. Correct.
  - Per-level losses: `rankedA15Loss_le_degree` gives `4rk + 2k² + 4k ≤ 10D²`; the level sum adds `D + 1 ≤ 2^{D²}`, for `11D²` in total. `adaptedA15TotalLoss_le_degree` gives `2k² + 4k ≤ 11D²`. Both correct.

**F6: documentation drift.** Severity: low.

- The `selected_actual_event_moment_bound` docstring calls `hdecomp` "the sole remaining … obligation". That obligation is discharged in `selected_actual_reconstructed_holder_bound`.
- `selected_actual_analytic_rhs` and `matching_center_mass_eq_grassmann_beta` are introduced with `/-! … -/` module comments, so those notes are not attached to the declarations.
- `exists_dyadic_exponent_for_actual_moment` is unused.
- `hm : 256 ≤ m` in `selected_rankloss_exponent` is only used for positivity.

**F7: duplicate local instances.** Severity: low.

- Several files declare their own local `Fintype` instances for linear-map spaces, using both `FunLike.fintype` and `Fintype.ofFinite`.
- This doesn't change meaning, because `Fintype` is a subsingleton and the build closed.
- Downstream callers might see instance mismatches when they apply these statements. That would be an elaboration issue, not a soundness issue.

## Checks with no concerns

- **A16 chain.** `filteredCarrierFunction_energy_le_A16` is a properly conditional statement: it assumes Fourier support through `D` and the original up-to-`D` actual globalness, and nothing is assumed about the endpoint.
  - The zero-carrier branch reduces to the order-0 restriction `⟨⊥, ⊤, 0⟩`.
  - Low ranks are killed by the selected-rank lower bound (`selected_frequency_rank_lower_bound`).
  - Retained levels are orthogonal because their residual ranks are distinct.
  - The tower-endpoint, bottom/top re-indexing and Bessel steps go in the correct directions.
- **Star law.** `starLaw_atom` correctly factors the uniform distribution on the sigma type, using the uniform extension count (`starTuple_card`).
- **Conditional complement count.** `card_conditional_complements` gives `2^{(dim C − dim K)·dim H}`, through the bijection between complements and graph maps that vanish on the fixed center.
- **Threshold step.** In `actual_append_threshold_pointwise`, both the good case and the bad case are valid for every `m`, including `m = 0`.

## Open questions for integration (outside this partition)

- Does the HC46 original application file remove the hHC premise (F1)? Its axiom output also needs checking.
- The definition of `PseudorandomExact`: whether `eta < 0` is impossible (F3) and whether the exact budget implies lower orders (F4).
- Whether Spectral47 is true and inhabited (F2).
- The cross-partition lemmas this partition relies on: `selected_spectral_parameters`, `actual_leaf_failed_zoom_gives_nominal_pseudorandom`, `matchingStarMass_cast_le_twice_actualAppendRankImageMoment`, append cross-level orthogonality, `finite_sum_lpNorm_le`, and the typed A14/A15 one-step and `manuscript_A1_complex` lemmas.
- The external Init/Mathlib/Batteries libraries are trusted at their pinned versions, not newly reviewed here. That includes `Real.compact_inner_le_weight_mul_Lp_of_nonneg`.
- Still open per scope: the broader Spectral47, source/star/robust8S/numericNO, encoded reduction, runtime/learning, upstream bridges, and the manuscript/render/novelty gates.
