# Complexity review: Full89, partition 6/9 (original A22 / HC46 / selected consumer)

**Verdict: GO-WITH-NOTES** for this partition only. This is not a whole-campaign verdict.

I read every proof body in all 21 supplied files. I did not run Lean, use tools, write files or start subagents. Whether these files compile and which axioms they use rests on your GCP receipt. My contribution is a reading of statements, assumptions, quantifiers, exponents and proof direction.

I don't give line numbers because I had no tools to count lines reliably. Each finding is anchored to a declaration name, which is unique within its file.

## Per-file inspection status

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46DR6Incidence.lean | Inspected (all bodies) |
| 2 | ActualBinaryMatrixHC46DR6Mobius.lean | Inspected |
| 3 | ActualBinaryMatrixHC46DR6Moment.lean | Inspected |
| 4 | ActualBinaryMatrixHC46DR6SignMoments.lean | Inspected |
| 5 | ActualBinaryMatrixHC46FourierA16.lean | Inspected |
| 6 | ActualBinaryMatrixHC46OriginalExactInhabitantChecks.lean | Inspected (only `#check`/`#print axioms`; the target declarations are not in this partition) |
| 7 | ActualBinaryMatrixHC46RealQNorm.lean | Inspected |
| 8 | ActualBinaryMatrixHC46RealQNormChecks.lean | Inspected (checks only) |
| 9 | ActualBinaryMatrixHC46RealQTransport.lean | Inspected |
| 10 | ActualBinaryMatrixHC46RealQTransportChecks.lean | Inspected (checks only) |
| 11 | ActualBinaryMatrixHC46T2Transfer.lean | Inspected |
| 12 | ActualBinaryMatrixHC46TypedA14Energy.lean | Inspected |
| 13 | ActualBinaryMatrixHC46TypedFourierTransport.lean | Inspected |
| 14 | ActualChangedAmbient8SBoundary.lean | Inspected |
| 15 | ActualFiniteDegreeFourierProduct.lean | Inspected |
| 16 | ActualFiniteDegreeFourierReconstruction.lean | Inspected |
| 17 | ActualFixedFunctionalMatrixLift.lean | Inspected |
| 18 | ActualFixedFunctionalStarMoment.lean | Inspected |
| 19 | ActualLeafLabelRankImageAlignment.lean | Inspected |
| 20 | ActualMZ24HyperplaneSupport.lean | Inspected |
| 21 | ActualMaximalPairLadder.lean | Inspected |

No body was skipped.

## Substantive audit

### DR6 headline theorem: `dr6_actual_complex_fourth_moment_over_162_le` (Moment)

**Premises.** The only premise is `ComplexFourierSupportedThrough D f`. There is no hHC, scalar-F2, rank-guard, reality or Booleanity premise. The support premise can be satisfied (it holds trivially whenever `D ≥ d`), so the theorem is not vacuous. All `D` are covered: `D = 0` gets its own proof via constancy (`dr6_constant_of_complex_support_zero`), and `D ≥ 1` goes through the incidence argument.

**Exponent chain.** Every step checks out:

- **F1 term, 2^(6D²):** the outer split count gives 2^(rank X²) ≤ 2^(4D²) when rank X ≤ 2D. The coefficient mass is ≤ 2^(D²)·‖f‖₂², and squaring it gives 2^(2D²). Total: 4D² + 2D² = 6D².
  - Outputs with rank X > 2D have zero F1 mass (`hpoint` in `dr6_actual_f1_total_energy_le_parseval`).
  - Mapping (X, A, B) to (A, B) is injective because X = A + B.
  - Each Gram entry satisfies H(A,B)² ≤ R(A)·R(B) by Cauchy–Schwarz.
- **F2 term, weight 2^(7D(i+j)):**
  - Möbius weight: α_k² = 2^(2⌊k(k−1)/2⌋) ≤ 2^(k(k−1)) ≤ 2^(Dk) for k ≤ D, which gives 2^(D(i+j)) (`dr6_mobiusAlpha_sq_le_pow`).
  - Carrier count: ≤ 2^(rank X·(i+j)) ≤ 2^(2D(i+j)) (`dr6_f2_outerCarrier_pair_card_le`).
  - Weighted Cauchy with c = 2^(2D(i+j)) contributes a factor of 2^(4D(i+j)).
  - Total: 1 + 2 + 4 = 7.
- **The 31/225 factor:** the sum of 2^(−4D(i+j)) over the grid without its (0,0) term is ≤ (16/15)² − 1 = 31/225. This needs D ≥ 1, which is supplied.
- **Combining:** E|f|⁴ ≤ 2a + (62/225)·S, and dividing by 162 gives ≤ a + S. The constant 162 is valid but very loose; the same chain already gives the bound with 2 in place of 162.

**Proof direction is sound throughout:**

- Parseval runs from the fourth moment to the sum of squared convolution coefficients.
- The convolution fibre is partitioned into F2 and its complement. Each complement pair is sent to an F1 pair by coverage, and the injectivity is proved.
- Grades above D vanish exactly because of Fourier support (`dr6_complexFilter_eq_zero_of_grade_gt_support`).
- The (X-dependent grid) → (fixed D-grid) → (all nonzero (A,B)) steps are injections into nonnegative terms. A nonzero grade forces `A ≠ ⊥ ∨ B ≠ ⊤`, and the dimensions recover the grade, so there is no double counting.

**Signed incidence.** The q-binomial identity Σ_k G(n,k)(−1)^k 2^(k(k−1)/2) = ∏_{i<n}(1 − 2^i) is proved inductively from the actual Gaussian recurrence. The product contains the i = 0 factor (1 − 1) = 0, so it is 0 for n ≥ 1, which gives the indicator 1_{n>0}.

The kernel side goes through the coordinate dual annihilator and order reversal (`dr6KernelSuperspacesEquiv`). The (0,0) grid entry is excluded only by the weight convention, and the grid factorization reproduces I + K − IK exactly. Every coefficient stays in ℂ until the obstruction identity is established, so no absolute values are taken early.

### Real-q / A22 infrastructure (RealQNorm, RealQTransport)

- `pConjugate p = p/(p−1)` is the exact real conjugate exponent with no rounding, and `pConjugate_holder` requires p ≥ 2.
- `realQNorm_holder` is normalized Hölder: the factors N^(1/p)·N^(1/q) cancel to N exactly.
- Minkowski, scaling, monotonicity, finite-sum and equivalence-invariance lemmas are all derived directly from Mathlib.
- **`exactPR_to_actual_LqGlobal`** takes an arbitrary real eta and caps it with `min eta 1`. For a Boolean indicator, ‖1_b‖^q equals normSq (this uses q > 0 for 0^q = 0). The fibre energy is then ≤ min(eta, 1), and the norm equals the energy raised to 1/q = 1 − 1/p.
  - For eta < 0, the premise appears unsatisfiable (the energy is ≥ 0), so the result holds vacuously there. That needs confirming against `PseudorandomExact`, which is in another partition. For eta ≥ 1 the bound is the trivial value 1.
  - So "unrestricted eta" is stated honestly, and no hHC premise is introduced.
- `UpToActualLqGlobal` includes the order-0 whole-space fibre, so `_parameter_nonneg` and `_whole_space` are genuine consequences.
- The equivalence between raw and actual globalness requires nonempty fibres only on the raw side, and actual fibres always contain their base.
- The column, row and transpose transports lose exactly one unit of budget.

## Findings

| ID | Severity | Declaration / location | Finding |
|---|---|---|---|
| N1 | Low (documentation) | DR6Moment module docstring | Says the final inequality "is authored source only and remains uncompiled and uncertified." This contradicts the GCP receipt. Whichever is wrong, the docstring is stale and misstates the evidence status. |
| N2 | Low (documentation) | DR6Incidence module docstring; docstring of `dr6_f2_a5_global_XGradeEnergy_bound` | Both say the global X-carrier enlargement and F2 combination "remain open" / "does not certify the complete DR6 theorem." The same file now proves `dr6_f2_a5_XGradeEnergy_le_fixed_D_ambient` and `dr6_f2_a5_global_fixed_D_ambient_bound`. Stale. The DR6Mobius header ("Neither milestone proves the signed A5 incidence reindexing") is true of that file alone but stale for the campaign. |
| N3 | Low (structure) | DR6Incidence, the `end` just before `dr6_f2_a5_global_fixed_D_ambient_bound` | A stray `end` closes the `noncomputable section` early. The final theorem therefore sits outside the scope of the `Classical.propDecidable` and `Fintype.ofFinite` local instances. It compiled and Moment consumes it through `simpa [..._eq_grid]`, so it's harmless, but the instance paths differ from the rest of the file. |
| N4 | Low (premise does nothing) | T2Transfer `t2_right_complement_energy` | The premise `h : t2RightSelected …` is used only for the unused `_hcan`. The conclusion (one nonnegative term ≤ the full sum over pairs) holds for every (C, H). It must not be counted as evidence of T2 energy transport. |
| N5 | Info | Moment `dr6_actual_complex_f2_remainder_eq_signedCoefficient` | Has an implicit `D` that never appears in the statement. Harmless. |
| N6 | Info | MaximalPairLadder `DecodedPair Q d` | `d` is a phantom type parameter (no field uses it); it only becomes meaningful through `Zoom`/`Grass V d` at use sites. Also, `maximalPairLadder` assumes `4B ≤ agreement` but only uses `B ≤ agreement`. |
| N7 | Info (conditional, not universal) | ChangedAmbient8S `first_inverse_witness_of_eightS` | Conditional on `AllAmbientInverse`, which is a `def … : Prop`, not an axiom, and is not discharged here. The theorem itself is only the monotone step S ≤ 8S ≤ density. Consistent with robust8S remaining open. |
| N8 | Info (conditional) | FixedFunctionalMatrixLift `failed_zoom_gives_*`; LeafLabel `actual_leaf_failed_zoom_gives_nominal_pseudorandom` | Conditional on `hfail` (every budget-r nonempty zoom has agreement ≤ e) together with r < d and e ≥ 0. The factor 2 comes from `exact_zoom_implies_nominal_pseudorandom`, which is in another partition. |
| N9 | Info | StarMoment `set_option backward.isDefEq.respectTransparency false`; T2 `maxHeartbeats 1500000` | These affect elaboration only; the kernel check is unaffected. Recorded for integration hygiene. |
| N10 | Info | MaximalPairLadder header comment | An embedded old receipt ("d93d23b … Lean 4.34.0-rc2") is a provenance comment, not evidence for this milestone. |

None of these is a soundness blocker.

## Open questions for integration (cross-partition and external boundaries)

1. **Original HC46.** The statements of `original_HC46_exact`, `_boolean_second`, `_boolean_mean_le_one`, `_zero_of_energy_zero`, `_moment_density_algebra` and `_moment_to_norm` are not in this partition; file 6 only `#check`s them. Whether eta is unrestricted and whether any hHC premise is present has to be confirmed in the partition that holds `ActualBinaryMatrixHC46OriginalExactInhabitant.lean`.
2. **Real-q A22 consumer.** The theorem that actually consumes `realQNorm`/`pConjugate`/`UpToActualLqGlobal` (A22 and the selected consumer) is not here.
3. **Convolution partition.** Needed: the definitions of `DR6F2Obstruction`, `DR6F1Witness`, `DR6DirectYDecomposition`, and `dr6_matrix_f1_or_f2_coverage` / `dr6_y_decomposition_card_le_pow`. In particular, `dr6_f2_actual_union_iff_manuscript_obstruction` is proved by `unfold` + `simp only`, so `DR6F2Obstruction` must literally be the image-meet-≠-⊥ ∨ kernel-join-≠-⊤ predicate. Please confirm it matches the manuscript.
4. **Other definitions used here:** `DR6OrdinarySelected` (A17), `complex_fourier_parseval` (A12), `W6Grass`/`w6_card_grass*`/`w6Gaussian` (A7), `PseudorandomExact`/`exactPR_to_actual_normSqGlobal`/`fibreEnergy`, the affine restriction API (`actualOfRaw`, `rawOfActual`, `liftRestriction`, `transposeRaw`), `ExactBudgetZoomBound`, and `typed_A14_fixedLine`/`fixedHyperplane`.
5. **Manuscript match** for the DR6 constants 162, 2^(6D²) and the 2^(7D(i+j)) weight.
6. **External boundary:** Mathlib lemmas such as `Real.inner_le_Lp_mul_Lq_of_nonneg`, `Real.Lp_add_le_of_nonneg`, the `Subspace.dualAnnihilator`/`dualCoannihilator` lemmas, `isSimpleModule_iff_finrank_eq_one` and `Finset.sum_mul_sq_le_sq_mul_sq` are trusted from the pinned library source, not newly reviewed here.

Still open and outside this partition, as you stated: broader Spectral47; source/star/robust8S/numericNO/encoded reduction/runtime/learning; upstream bridges; manuscript/render/novelty gates.
