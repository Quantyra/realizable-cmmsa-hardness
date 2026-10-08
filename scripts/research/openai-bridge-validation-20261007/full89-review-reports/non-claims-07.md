# Partition 7/9 non-claims review: Full89 A22/HC46/selected-consumer milestone

**Verdict: GO-WITH-NOTES.** This verdict covers only this partition and is not a verdict on the whole campaign.

I read all 35 supplied files in full and skipped none. The proofs here hold together, and every analytic contract appears as an explicit premise. Two caveats limit what this partition can support:

- **The hHC-free claim is not shown here.** The selected consumer in this partition, `selected_actual_material_moment_bound`, still takes `hHC : HC46ExactContract` as a premise (finding F1). An hHC-free consumer is not shown here; it would have to come from another partition.
- **A22 is not here.** None of the 35 files contains real-q A22, so I could not audit it.

I followed your constraints: no tools, no writes, no code execution. Because of that, I did not check the SHA256 values against the source index and did not see the `#print axioms` output. I rely on the stated scope (172 standard axiom profiles) for axioms. I cite findings by declaration name; line numbers are approximate (≈) because I could not open the indexed files.

## File inventory

All 35 files below were inspected in full.

| # | File | SHA256 (as supplied) |
|---|---|---|
| 1 | ActualSelectedComplementAnalyticMoment | BFAE5D2E… |
| 2 | ActualSelectedComplementAppendMoment | 1D84E044… |
| 3 | ActualSelectedComplementHC46OriginalApplicationChecks (commands only; nothing to prove) | FCF92E8E… |
| 4 | ActualSourceStarLaw | DC4EC18D… |
| 5 | ActualTaggedConditionalGraphCount | F470E0BB… |
| 6 | ActualTypedABArbitraryRankProjection | 9D3996B9… |
| 7 | ActualTypedABBottomTopRankReindex | 05BEB119… |
| 8 | ActualTypedABCanonicalDCollapse | B36D006D… |
| 9 | ActualTypedABCanonicalEndpointCollapse | 07837527… |
| 10 | ActualTypedABCanonicalFlag | A8A0840E… |
| 11 | ActualTypedABCanonicalProjection | BDA8C9D8… |
| 12 | ActualTypedABCanonicalRankProjectionCollapse | 2BFFF551… |
| 13 | ActualTypedABCanonicalRankProjectionEnergy | 908F5072… |
| 14 | ActualTypedABCanonicalSignalCollapse | 74F4C00E… |
| 15 | ActualTypedABEndpointTransport | E8C79589… |
| 16 | ActualTypedABFullA16Assembly | BECC6381… |
| 17 | ActualTypedABFullA16Final | A592FF69… |
| 18 | ActualTypedABHybridSelectorSteps | BB3D711F… |
| 19 | ActualTypedABMixedTower | 3D09C9B8… |
| 20 | ActualTypedABOriginalGlobalBridgeClean | C7B1B0EF… |
| 21 | ActualTypedABProjectionEnergy | 1E8631A1… |
| 22 | ActualTypedABRankedTower | EAF4E5EB… |
| 23 | ActualTypedCarrierAmbientBudget | 612BE9D8… |
| 24 | ActualTypedFourierEquivNaturality | FDCADBA5… |
| 25 | ActualTypedIntrinsicHyperplaneNaturality | AD01E842… |
| 26 | ActualTypedIntrinsicWitnessNaturality | 25783B00… |
| 27 | BinaryMatrixA15A1Carrier | EE47AF74… |
| 28 | BinaryMatrixA15BaseCase | 35E410B4… |
| 29 | BinaryMatrixA15CanonicalLineRank | 176BD052… |
| 30 | BinaryMatrixA15CanonicalRank | FECCB4BE… |
| 31 | BinaryMatrixA15NestedHyperplane | 16421274… |
| 32 | BinaryMatrixA15NestedLine | F9083A80… |
| 33 | BinaryMatrixA15SelectedBridge | AE88C4B0… |
| 34 | BinaryMatrixA1CharacterBridge | 3B0A4D6E… |
| 35 | BinaryMatrixA1CoefficientTransfer | 499550B5… |

## Findings

**F1 — High (where the claim stops; not a proof defect). The selected consumer here still assumes HC46.**
- These declarations in `ActualSelectedComplementAnalyticMoment` all take `hHC : HC46ExactContract` as a hypothesis:
  - `selected_leaf_HC46_of_exact_PR`
  - `selected_leaf_append_level_HC46`
  - `selected_low_append_HC46_lpNorm_bound`
  - `selected_actual_HC_spectral_moment_bound`
  - `selected_actual_material_moment_bound`
- Nothing in this partition proves `HC46ExactContract`.
- The checks file (#3) names `selected_leaf_HC46_original` and `selected_leaf_failed_zoom_HC46_original`. Their source file, `ActualSelectedComplementHC46OriginalApplication.lean`, is not in this partition, and the checks file's output was not supplied.
- **Consequence:** `selected_actual_material_moment_bound` must not be cited as the hHC-free selected consumer. Integration needs to confirm one of two things:
  - that the original application proves the universal `HC46ExactContract`, or
  - that it re-runs this same consumer path (same `Tc`, `fc`, `r`, `k`, `eta = 2e`) without `hHC`.

**F2 — Medium (possible vacuity). With unrestricted eta, the HC46 contract can only hold if negative eta makes its premise impossible.**
- In `HC46ExactContract` (≈L35), the exponent `y = (p−2)/p` lies in [1/2, 1).
- For eta < 0, Mathlib's `Real.rpow` gives `exp(y·log|eta|)·cos(yπ)`, which is ≤ 0. The contract would then require `lpNorm = 0`.
- So the contract is true only if `PseudorandomExact r eta b` cannot hold when eta < 0 (and, at eta = 0, forces the level-i projection to vanish).
- `PseudorandomExact` is defined in another partition. If its definition admits negative eta, for example through empty zooms, the contract is false and every consumer taking `hHC` is vacuously true.
- This partition's consumer only ever uses eta = 2e ≥ 0, so the risk is to whether the universal contract can be satisfied at all, not to the specific instance.

**F3 — Medium (spectral contract is still an assumption).**
- `Spectral47ExactContract` (≈L45) is a premise of `appendHighLevel_energy_le_spectral_sum`, `selected_leaf_high_energy_le_spectral`, and the two moment theorems. This is consistent with your scope note that Spectral47 remains open.
- It is quantified over a caller-chosen `sourceHeightCutoff`. Integration must confirm that the cutoff instantiated through `analyticSourceHeightFloor`/`hsel` is the source's cutoff. A weaker cutoff turns the premise into a stronger, possibly false, contract.
- Its `hRho` requires only 0 < rho, with no upper bound. That is harmless, because `hc` forces h = 0 when rho > 1.

**F4 — Medium (numerical bound is not shown to be useful).**
- `selected_actual_analytic_rhs` is a raw expression. No theorem here shows it is below 1, or otherwise small.
- The low-rank term is about (Σ_{i≤r} 2^{500 i² k}·eta^{(k−2)/k})^m with k ∈ [4m, 8m). Its prefactor is up to roughly 2^{4000 r² m²}, which eta^{≈m} must overcome.
- The high-rank energies E[(P_i 1_F)²] are left unbounded, with a free threshold `a`.
- The shape of the 2^{500 i² p} constant needs checking against the source statement of HC4.6. That source is not in this partition.

**F5 — Low (quantifier alignment across partitions).**
- `hfail` in `selected_actual_material_moment_bound` and `selected_leaf_failed_zoom_PR` fixes `q + codim = r` exactly.
- The conversion to `PseudorandomExact r` happens in `ActualLeafLabelRankImageAlignment`, which is in another partition. Integration should confirm that "exactly r" versus "at most r" lines up there.

**F6 — Info (stale docstring).**
- `selected_actual_event_moment_bound` says `hdecomp` is "the sole remaining … obligation".
- That obligation is already discharged by `selected_append_low_high_decomp` inside `selected_actual_reconstructed_holder_bound`. Only the comment is out of date.

## What I verified (proof direction and exponent arithmetic)

**Selected moment chain.** Every step bounds the acceptance mass from above, which is the direction needed:
- matching-star mass ≤ 2·moment (`selected_actual_append_moment`). Its rank-loss budget checks out: c + m·s + 2h ≤ 2h² < 2J, using m + 2 ≤ h.
- moment ≤ the good/bad-event split (`actual_append_threshold_pointwise`). Both cases are correct, including m = 0.
- Hölder with the center weight exponent beta^{1 − m/k}, where beta comes from `selected_center_matrix_mean_le_exact_grassmann_beta` (derived using alpha ≤ 1, not assumed).
- Minkowski over levels, then Jensen per fiber, then HC46 per level.
- The low/high split is exact Fourier reconstruction; it is not supplied by the caller.

**Same consumer throughout.** `selected_actual_material_moment_bound` uses the same `Tc`, `fc`, `r`, `e` for the failed-zoom pseudorandomness premise and for the moment. `selected_actual_moment_def` pins the selected center, leaf, and shared base by `rfl`. The center identity (`matching_center_mass_eq_grassmann_beta`) is exact.

**A15/A16 stack (files 6–35).** Each declaration's statement follows from its listed premises:
- `ranked_tower_terminal_global` and `adapted_tower_terminal_global` multiply one-step losses of 4·2^{4(k+1)}.
- The closed forms check:
  - 2^{4rk + 2k² + 4k} ≤ 2^{10D²} (`rankedA15Loss_le_degree`).
  - 2^{2k² + 4k} ≤ 2^{11D²} (`adaptedA15TotalLoss_le_degree`).
  - (D+1)·2^{10D²} ≤ 2^{11D²} (`count_le_two_pow_sq`).
- `filteredCarrierFunction_energy_le_A16` handles the zero-carrier case directly and removes low ranks via `selected_frequency_rank_lower_bound`. Orthogonality is derived (`typedComplexRankProjection_cross_orthogonal`), not assumed. Its premises are Fourier support through D and actual up-to-D globalness.
- `liftCarrierRestriction_order` makes the ambient-to-carrier order cost explicit. The A16 bridge uses only the bottom/top carrier (`actual_global_to_bottomTop_typed`), where that cost is zero.

**Other files.**
- `ActualSourceStarLaw` defines the star law and proves that each point mass is a uniform center times independent uniform extensions (`starLaw_atom`).
- `card_conditional_complements` is an exact count.
- Character and coefficient transfer use the orthogonality lemma with all collisions kept.

## Left open for integration

1. Whether the original application proves `HC46ExactContract` or re-runs this consumer without `hHC` (F1).
2. The definition of `PseudorandomExact` and how it behaves for eta ≤ 0 (F2).
3. Real-q A22, which is not in this partition.
4. Several bridges imported from other partitions, which I treated as accepted inputs:
   - `matchingStarMass_cast_le_twice_actualAppendRankImageMoment`
   - `actual_leaf_failed_zoom_gives_nominal_pseudorandom`
   - `actualLeafIndicator_mul_right_eq`
   - `selected_spectral_parameters`
   - the `ActualFiniteMomentLpBounds` lemmas
   - the A14/A15 one-step theorems
   - `ActualBinaryMatrixHC46A18SourceGlobal`
5. Whether the A16 result here actually feeds an HC46 proof. Nothing in this partition consumes it.
6. Spectral47 (F3) and whether the bounds are numerically useful (F4).
7. The Init/Mathlib/Batteries boundary: trusted as pinned library code, not reviewed here. That includes `Real.compact_inner_le_weight_mul_Lp_of_nonneg` and how `Real.rpow` handles negative bases.
