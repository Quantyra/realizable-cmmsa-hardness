# Proof-adversarial review: Full89 partition 7/9 (A22/HC46 selected consumer)

**Verdict for this partition: GO-WITH-NOTES.** This verdict covers only these 35 files. It is not a verdict on the whole campaign and does not mean the milestone is accepted unconditionally.

**Scope and limits**
- I made no tool calls. I did not open `source-index.json` and did not recompute the SHA-256 hashes; I'm relying on the hash labels in your message.
- I checked the proofs by reading them. I did not type-check them. That the files compile, have the stated axiom profiles and close all trace nodes is your supplied GCP evidence; I did not reproduce it.
- I had no tool to number lines, so references below are by declaration name.

## File coverage (35 supplied, 35 inspected, 0 skipped)

All of these were inspected in full:
1. `ActualSelectedComplementAnalyticMoment.lean`
2. `ActualSelectedComplementAppendMoment.lean`
3. `ActualSelectedComplementHC46OriginalApplicationChecks.lean`
4. `ActualSourceStarLaw.lean`
5. `ActualTaggedConditionalGraphCount.lean`
6. `ActualTypedABArbitraryRankProjection.lean`
7. `ActualTypedABBottomTopRankReindex.lean`
8. `ActualTypedABCanonicalDCollapse.lean`
9. `ActualTypedABCanonicalEndpointCollapse.lean`
10. `ActualTypedABCanonicalFlag.lean`
11. `ActualTypedABCanonicalProjection.lean`
12. `ActualTypedABCanonicalRankProjectionCollapse.lean`
13. `ActualTypedABCanonicalRankProjectionEnergy.lean`
14. `ActualTypedABCanonicalSignalCollapse.lean`
15. `ActualTypedABEndpointTransport.lean`
16. `ActualTypedABFullA16Assembly.lean`
17. `ActualTypedABFullA16Final.lean`
18. `ActualTypedABHybridSelectorSteps.lean`
19. `ActualTypedABMixedTower.lean`
20. `ActualTypedABOriginalGlobalBridgeClean.lean`
21. `ActualTypedABProjectionEnergy.lean`
22. `ActualTypedABRankedTower.lean`
23. `ActualTypedCarrierAmbientBudget.lean`
24. `ActualTypedFourierEquivNaturality.lean`
25. `ActualTypedIntrinsicHyperplaneNaturality.lean`
26. `ActualTypedIntrinsicWitnessNaturality.lean`
27. `BinaryMatrixA15A1Carrier.lean`
28. `BinaryMatrixA15BaseCase.lean`
29. `BinaryMatrixA15CanonicalLineRank.lean`
30. `BinaryMatrixA15CanonicalRank.lean`
31. `BinaryMatrixA15NestedHyperplane.lean`
32. `BinaryMatrixA15NestedLine.lean`
33. `BinaryMatrixA15SelectedBridge.lean`
34. `BinaryMatrixA1CharacterBridge.lean`
35. `BinaryMatrixA1CoefficientTransfer.lean`

## Findings

### F1 — HIGH (to resolve at integration): every HC46 use here is conditional on an `hHC` premise
- In `ActualSelectedComplementAnalyticMoment`, these theorems all take `hHC : HC46ExactContract`:
  - `selected_leaf_HC46_of_exact_PR`
  - `selected_leaf_append_level_HC46`
  - `selected_low_append_HC46_lpNorm_bound`
  - `selected_actual_HC_spectral_moment_bound`
  - `selected_actual_material_moment_bound`
- The last two also take `hSpectral : Spectral47ExactContract`.
- Nothing in this partition proves either contract. The file's own docstring says they are "source-shaped interfaces, not claims … proved locally."
- The theorems that would supply the premise-free path (`selected_leaf_HC46_original` and `selected_leaf_failed_zoom_HC46_original`) are only named by `#check` / `#print axioms` in the Checks file. Their module, `ActualSelectedComplementHC46OriginalApplication`, is not in this partition.
- **So the "no added hHC premise" claim cannot be confirmed here.** Integration has to show that those theorems use the same selected `T`, `f` and `rankImageBoolean (leafMatchBit …)` without an `HC46ExactContract` argument, and that their axiom output is standard.

### F2 — HIGH (to resolve at integration): HC46ExactContract might be self-contradictory, which would make F1's consumers vacuous
- The contract quantifies over all `r`, all real `eta` and all `p = 2^q ≥ 4`. It has no `r ≤ d` (or `r ≤ n+d`) guard and no `0 ≤ eta` guard.
- `hfail` in `selected_leaf_failed_zoom_PR` constrains zooms of order *exactly* `r` (`q + codim P.W = r`). That suggests `PseudorandomExact r eta b` is an exact-order condition. Its definition is not in this partition.
- If it is exact-order, it holds vacuously once `r` is larger than the maximum restriction order. Then:
  - Take `eta = 0`, `i = 0`, `p = 4` and `b ≡ true`. The contract says `|mean b| ≤ 0`, which is false.
  - Take `eta < 0` and `p = 8`. `Real.rpow` gives `eta^(3/4) = |eta|^(3/4)·cos(3π/4) < 0`, so the bound is negative.
- In either case `HC46ExactContract` is refutable, and every theorem in F1 is vacuously true.
- **Integration must check from the definition of `PseudorandomExact` that it is never vacuous and forces `eta ≥ 0`.**
- For `eta ≥ 1` the contract reduces to the ε = 1 global-hypercontractivity bound for arbitrary Booleans. That looks plausible from the source but is not shown here. The selected application itself uses `r < c+s` and `eta = 2e` with `e ≥ 0`, so it stays inside the safe range.

### F3 — Note: Spectral47ExactContract looks consistent
- I sanity-checked it by hand; this is not machine-checked.
- Because `F` is invariant under right multiplication by invertible matrices, each Fourier coefficient depends only on the column space of its frequency.
- The fraction of rank-`i` frequencies of the form `[Y₁|0]` with a given column space is ∏_{j<i}(2^c−2^j)/(2^{c+s}−2^j) ≤ 2^{−is}. That is below the stated 2^{−i(s−1)} + 3·2^{i−n}.
- The edge cases (h = 0, ρ = 1, i > c) are benign. So `hSpectral` is unlikely to be a source of vacuity, though it is still unproved (Spectral47 remains open).

### F4 — MEDIUM: one docstring could be over-read
- `selected_actual_material_moment_bound` is described as a "derived HC/spectral moment bound", but it still takes `hHC`, `hSpectral` and `hfail`.
- It is a conditional result, not a universal one, and integration should cite it that way.
- `hfail` (failed-zoom agreement ≤ e) is a real, non-vacuous premise. The selector equation forces m ≥ 256, so `hm` and `hp` are satisfiable.

### F5 — Checked correct (proof direction, quantifiers, numerics)
- **Threshold step** (`actual_append_threshold_pointwise` and its mean version):
  - Good case: A^m ≤ (|L|+a)^m ≤ 2^m(|L|^m + a^m).
  - Bad case: A^m ≤ 1 ≤ H²/a².
  - The weight g ∈ [0,1] is preserved, and m = 0 is fine.
- **Real-exponent Hölder** (`selected_low_weighted_holder`):
  - Inequality: E[g|L|^m] ≤ E[g]^{1−1/q}·E[g|L|^{mq}]^{1/q}.
  - With m = 0 the premise `1 ≤ p/0` is false, so the theorem is vacuous there.
  - In the material theorem m ≥ 256, so this case is not reached.
  - The weight is bounded by β through `rpow_le_rpow` with a nonnegative exponent.
  - Raising to the m/k power goes in the right direction (`hlowroot`).
- **Low part:**
  - Minkowski over i ≤ r, then fiberwise Jensen, then HC46 per level, applied only when `i ≤ r`.
  - Level i = 0 (the mean) is included.
- **High part:** cross-level orthogonality after appending is true unconditionally, since appending averages out any frequency with a nonzero block on the appended columns.
- **Exponent window** (`exists_dyadic_moment_exponent_window`): 4m ≤ k < 8m with k dyadic.
- **Constants in the final bound** (with k as the moment exponent):
  - level-i factor: 2^{500·i²·k}, with total low-part cost up to (r+1)^m·2^{500·r²·k·m} ≤ (r+1)^m·2^{4000·r²·m²};
  - β exponent: 1 − m/k ∈ [3/4, 7/8);
  - η exponent: m(k−2)/k ≥ m − 1/2.
  
  Whether these numbers are useful downstream is out of scope.
- **Append-moment file:**
  - `selected_rankloss_exponent` gives c + m·s + 2h ≤ 2h² < 2J, using m+2 ≤ h and h² < J.
  - The rank-loss factor is ≤ 1/2, which gives the factor 2.
  - The center-mass identity is exact.
- **A16 chain** (`filteredCarrierFunction_energy_le_A16`):
  - Ranks below dim A + codim B are annihilated (`selected_frequency_rank_lower_bound`, logic checked).
  - Each retained level costs `rankedA15Loss` = 2^{4rk+2k²+4k} ≤ 2^{10D²}; the closed form checks out.
  - Bessel contraction goes the right way.
  - Distinct residual ranks are orthogonal.
  - D+1 ≤ 2^{D²}, giving the final 2^{11D²}. The k = 0 case is handled separately through the order-0 fibre.
  - Its premises are support through D plus original globalness, both stated explicitly. Nothing is hidden.
- **Other files** (star law, conditional graph count, flags, endpoint transport, naturality, A15 nested/canonical files): I found no defects.

### F6 — LOW (hygiene)
- `hklt` is unused inside the proof of `selected_actual_HC_spectral_moment_bound`. It is harmless, and the material theorem re-exports it as a conclusion.
- `selected_actual_analytic_rhs` and `matching_center_mass_eq_grassmann_beta` sit under `/-! … -/` module comments instead of `/-- … -/` docstrings.
- In `ActualTypedABMixedTower`, the `noncomputable section` is closed partway through the file, and one docstring is attached to `adaptedA15TotalLoss_le_degree` although it describes the next theorem. Cosmetic only.

## Open questions for integration
1. **Premise-free path:** does `ActualSelectedComplementHC46OriginalApplication` prove the selected-leaf HC46 bound without `HC46ExactContract`, using the same selected consumer (F1)?
2. **Contract consistency:** is `PseudorandomExact` non-vacuous for every `r`, and does it force `eta ≥ 0` (F2)?
3. **External boundaries:** these lemmas come from outside this partition and need to be checked there:
   - `ActualFiniteMomentLpBounds`
   - `matrix_grassmann_identity`, `alpha_bounds`, `grassmannExperiment_zero_copies`
   - `matchingStarMass_cast_le_twice_actualAppendRankImageMoment`
   - `uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero`
   - `actual_leaf_failed_zoom_gives_nominal_pseudorandom`
   - `typed_line_oneStep_A15_global` and `typed_hyperplane_oneStep_A15_global`
   - `manuscript_A1_complex`
   - `Real.compact_inner_le_weight_mul_Lp_of_nonneg`
   
   Init/Mathlib/Batteries are trusted as pinned library code, not newly reviewed here.
4. **Still open beyond this partition:** Spectral47; the source/star/robust8S/numericNO/encoded reduction/runtime/learning lanes; upstream bridges; and the manuscript/render/novelty gates.
