# Partition 1/9 review: Full89 original A22, HC46 and the selected consumer

**Verdict: GO-WITH-NOTES.** This verdict covers only this partition. It is not a verdict on the whole campaign.

I found no blocking issues in the 30 supplied files. Every theorem body was read in full. I relied on the supplied GCP results for compilation; nothing was run or rebuilt. I did not recompute any SHA256 values. I also did not read the source index or the 172-theorem list, because tools were not allowed. Mapping this partition's declarations onto the 172 list is therefore left for integration.

## 1. File inventory (every supplied complete file)

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46A22OriginalInduction | Inspected, all bodies |
| 2 | ActualBinaryMatrixHC46A22ParentFactorization | Inspected, all bodies |
| 3 | ActualBinaryMatrixHC46OriginalExactInhabitant | Inspected, all bodies |
| 4 | ActualSelectedComplementHC46OriginalApplication | Inspected, all bodies |
| 5 | ActualBinaryGrassmannIncidence | Inspected, all bodies |
| 6 | ActualBinaryMatrixHC46 | Inspected, all bodies |
| 7 | ActualBinaryMatrixHC46A11WeightedAggregate | Inspected, all bodies |
| 8 | ActualBinaryMatrixHC46A12FourthMoment | Inspected, all bodies |
| 9 | ActualBinaryMatrixHC46A12InfluenceBound | Inspected, all bodies |
| 10 | ActualBinaryMatrixHC46A17AdaptedLineDecomposition | Inspected, all bodies |
| 11 | ActualBinaryMatrixHC46A17CodomainBranch | Inspected, all bodies |
| 12 | ActualBinaryMatrixHC46A17DerivativeCoordinate | Inspected, all bodies |
| 13 | ActualBinaryMatrixHC46A17DerivativeGlobalTransfer | Inspected, all bodies |
| 14 | ActualBinaryMatrixHC46A17DomainBranch | Inspected, all bodies |
| 15 | ActualBinaryMatrixHC46A17DomainFrequencyCovariance | Inspected, all bodies |
| 16 | ActualBinaryMatrixHC46A17FixedSlice | Inspected, all bodies |
| 17 | ActualBinaryMatrixHC46A17Full | Inspected, all bodies |
| 18 | ActualBinaryMatrixHC46A17GenericParentCoverage | Inspected, all bodies |
| 19 | ActualBinaryMatrixHC46A17GenericParentEnergy | Inspected, all bodies |
| 20 | ActualBinaryMatrixHC46A17HomogeneousLineDecomposition | Inspected, all bodies |
| 21 | ActualBinaryMatrixHC46A17ParentFibreBridge | Inspected, all bodies |
| 22 | ActualBinaryMatrixHC46A17TransposeHybridFilter | Inspected, all bodies |
| 23 | ActualBinaryMatrixHC46A18AmbientHyperplaneLaw | Inspected, all bodies |
| 24 | ActualBinaryMatrixHC46A18CodomainNormalEnergy | Inspected, all bodies |
| 25 | ActualBinaryMatrixHC46A18Conditioning | Inspected, all bodies |
| 26 | ActualBinaryMatrixHC46A18DerivativeRankProjection | Inspected, all bodies |
| 27 | ActualBinaryMatrixHC46A18EnergyTriangle | Inspected, all bodies |
| 28 | ActualBinaryMatrixHC46A18FullFunctionalBridge | Inspected, all bodies |
| 29 | ActualBinaryMatrixHC46A18FullFunctionalEnergy | Inspected, all bodies |
| 30 | ActualBinaryMatrixHC46A18InductionBounds | Inspected, all bodies |

No files were skipped.

## 2. Core audit

### A22 (`manuscript_A22_actual`)
- **Premises:** only `UpToActualLqGlobal j (pConjugate p) eps f`, `2 ≤ p` and dyadic `p`. There is no hHC, influence or energy oracle among the premises.
- **Induction:** strong induction on `level`, with the induction hypothesis quantified over every `n' d' eta g`. The lower-level hypothesis is used only at `level-1`, on the reduced line and hyperplane witnesses, with parameter `2^(3j)·eps`.
- **The induction is not circular.**
  - Positive-cost parents are bounded by `B` using only the lower-level hypothesis (`a22_positive_parent_from_lowerIH`).
  - The zero-cost parent equals the energy `E` exactly (`a22_zero_cost_energy`).
  - If `E > B`, then `OriginalActualInfluenceThrough level E` is *derived* from those two facts (`hclose E le_rfl …`). Only then is `a22_dual_energy_of_influences` applied. The dual estimate's influence premise is therefore proved, not assumed.
  - Level 0 is handled separately; every parent has zero cost there.
- **Coverage of positive parents:** the case `A ≠ ⊥` goes through the domain line `span{x}`, `⊤`. The case `A = ⊥` goes through a containing hyperplane (`a22_exists_order_one_parent`). Together these cover every parent of positive cost.
- **Exponent checks, all verified by hand:**
  - `a22_dual_energy_of_influences`: with `p = 2m`, `200j²p² + 10j²(m−1) ≤ 810 j²m² ≤ 840 j²m² = 420j²p·m`.
  - The cancellation `E^m·E^m ≤ E^m·(c·eps²)^m ⇒ E ≤ c·eps²` uses `E > 0`; the case `E = 0` is split off.
  - `a22_positive_exponent`: `(j−1)² + j ≤ j²` and `6j ≤ 500jp`, so `B ≤ 2^(500j²p)eta²`. The final step uses `420 ≤ 500`.
- **Direction:** the Hölder pairing uses the exact projection identity `⟨Π_j f, f⟩ = ‖Π_j f‖²` (`a22_projection_pairing`), not idempotence alone. The resulting inequality runs in the correct direction (energy bounded above).

### HC46 contract (`original_HC46_exact`)
- **Unrestricted eta, including eta > 1 and eta = 0:** handled with `delta = min eta 1`.
  - `eta ≥ 0` is derived from the mean bound.
  - `delta = 0` forces `f = 0`, which is handled.
  - Rank `i = 0` delegates to `hc46_rank_zero_exact`, which also covers the `eta > 1` branch.
- **Exponent of delta:** the exponent `p − 2 + 2/p` is at least `p − 2`, and `delta ≤ 1`, so `rpow_le_rpow_of_exponent_ge` is applied in the correct direction.
- **Coefficient:** `200i²p² + (10i² + 500i²p)(p/2−1) ≤ 455 i²p² ≤ 500 i²p²` checks out.
- **Final step:** `delta ≤ eta` with a nonnegative exponent `(p−2)/p`.
- **Premises:** there is no added hHC premise. `hEven` is passed only to the rank-zero branch, which is harmless.

### Selected consumer
- `selected_leaf_HC46_original` discharges the contract with `original_HC46_exact`, so the contract is no longer a caller hypothesis.
- `selected_leaf_failed_zoom_HC46_original` composes this with `selected_leaf_failed_zoom_PR`, giving `eta = 2e`.

### Conditional statements versus universal claims
- **Universal:** `original_HC46_exact` and `manuscript_A7_actual`.
- **Universal under a stated premise:** `manuscript_A22_actual`, `manuscript_A12_actual` and `manuscript_A19_actual`, each under its own globalness or influence premise.
- **Conditional on caller-supplied premises:** `actual_A17_full_parent_energy` (needs `hsource`, the universal `hderiv` and `hD`), the A18 parent-fibre bounds, and `a22_parent_from_order_one_coordinate`.
- **Vacuity:** none found. From its uses, `OriginalActualInfluenceThrough` is "∀ A B T, cost ≤ r → a12Energy ≤ b", which has content. The degenerate "t = 0" genericity gate in the Grassmann file is documented in the source as vacuous on purpose.

### Other numerical checks verified
- **A11:** the A10 saving `100(D−t)² + 27Dt + 6Dk ≤ 100D² − 63Dt − 4Dk`, and both tail cases (`k > 0` needs `1 + 31D ≤ 32Dk`; `k = 0` needs `2 ≤ 32D`).
- **A12:** the selected-pair bound `2^(2·rank²) ≤ 2^(3D²)`, giving `103 = 100 + 3`. A19 then gives `114 = 103 + 11`.
- **A18 induction bounds:** the `9/512` budget absorption and the `1/961` geometric bound.
- **A17:** the triangle constant `2η₁ + 4·2^(2D)·η₂`.

## 3. Findings

None of these block the partition.

| # | Severity | Location | Finding |
|---|---|---|---|
| F1 | Low | `ParentFactorization.a22_parent_from_order_one_coordinate` | Not called anywhere in the supplied files. Its docstring says it is "applied only after… A14 witness and strict lower IH", which cannot be confirmed from what was supplied. Dead code or a stale claim. |
| F2 | Low | `ActualBinaryMatrixHC46.hc46_rank_zero_exact` docstring | Says "positive-rank estimate is the remaining HC46 engine step", which is out of date now that `original_HC46_exact` exists. |
| F3 | Low | `A17ParentFibreBridge` module docstring | Calls the matrix-lift identification "a separate theorem obligation", but `carrierAmbientLiftFibreEquiv_apply` proves it in the same file. Also, `carrierAmbientQuotientHomEquiv` takes a `T` argument it never uses. |
| F4 | Low / hygiene | `A17DomainFrequencyCovariance` | `set_option maxHeartbeats 800000` and `set_option diagnostics true` are left on a private theorem. `diagnostics` may emit info messages. Soundness is unaffected because the kernel checks the result. |
| F5 | Low / integration | `A11WeightedAggregate` | Uses `set_option backward.isDefEq.respectTransparency false`, which changes elaboration only; the kernel still checks the result. The confirmation that this run has no warnings should be checked to cover this option. |
| F6 | Informational | `A11WeightedAggregate` header | The docstring asserts prior acceptance ("frozen run 56… separate reviews"). I did not treat it as evidence. |
| F7 | Informational | `A17DomainBranch` / `A17CodomainBranch` / `A17Full` | `hDpos` (and probably `hr`) are not needed by the bodies. Unused premises make these statements conditional on more than they need, but do not affect soundness. |
| F8 | Informational | `a22_dual_energy_of_influences` docstring | Labels the lemma "A23" inside the A22 chain. Naming only. |
| F9 | Informational | `ActualBinaryGrassmannIncidence` | The gates use truncated natural subtraction (`… - 2*r`). The degenerate branches are harmless, no ratios or concentration are claimed, and these declarations do not feed the HC46 chain. |

## 4. Cross-partition and external-boundary questions for integration

These statements were not supplied here, and the soundness of this partition's chain depends on their exact form:

1. **`HC46ExactContract` definition:** confirm the quantifier order and premises. From the `intro` line, the contract is over `n d h r i p eta`, `d = 2h`, `PseudorandomExact r eta b`, `i ≤ r`, `p ≥ 4`, dyadic `p`. The conclusion should be the manuscript's unchanged bound `2^(500i²p)·eta^((p−2)/p)`.
2. **`exactPR_to_actual_LqGlobal`:** it must produce globalness through order `r` with parameter definitionally equal to `(min eta 1)^(1−1/p)`. This is the main analytic input that turns pseudorandomness into globalness. Also needed: `boolean_mean_le_of_exact`, `uniformMean_indicator_nonneg` and `complexRankProjection_boolean_eq`.
3. **Analytic lemmas used by A22:** the statements of
   - `actual_A18_original_global` and the definition of `OriginalActualInfluenceThrough` (A18OriginalGlobalInduction);
   - `manuscript_A21_actual`, assumed to have the form `2^(200D²p²)·E·ε^(p/2−1)`;
   - `realQNorm_holder_nat_pow`, `pConjugate`, `UpToActualLqGlobal_whole` and `UpToActualLqGlobal_parameter_nonneg`;
   - `a22_typed_line_witness_global`, `a22_typed_hyperplane_witness_global` and `a22_A14_coefficient_le` (`≤ 2^(3j)`), which carry the real-q operator bounds;
   - `typed_A14_fixedLine`, `typed_A14_fixedHyperplane` and `UpToActualLqGlobal_raw_typed`;
   - `a7_zero_order_component`.
4. **Consumers and lower layers:** `selected_leaf_HC46_of_exact_PR`, `selected_leaf_failed_zoom_PR`, `binary_hc_rankZero_exact`, `a7_positive_of_mixed_bound`, `manuscript_A7_degree_zero`, `filteredCarrierFunction_energy_le_A16`, and the A9/A8 fibre-charge lemmas.
5. **External libraries:** trust in Init, Mathlib and Batteries rests on the pinned kernel and library sources. That trust is explicit; those libraries were not reviewed as new proof here.
6. **Still open and outside this partition:** Spectral47, the source/star/robust8S/numericNO/encoded reduction/runtime/learning work, upstream bridges, and the manuscript/render/novelty gates.
