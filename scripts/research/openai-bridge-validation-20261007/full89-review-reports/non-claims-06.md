# Partition 6/9 non-claims review: Full89 A22/HC46 selected-consumer milestone

**Verdict: GO-WITH-NOTES.** All 21 supplied files were read in full. Nothing in this partition blocks the milestone. This verdict covers partition 6 only. It is not a verdict on the whole campaign or on A22 or HC46 as a whole.

**What this review did and did not do:**
- I had no tools and executed nothing. Compilation, the axiom profiles and the source closure are taken from the GCP receipt you supplied; I did not re-establish them.
- I did not compare the SHA256 values in the file headers against `source-index.json`, because I could not open it.
- The top-level `original_HC46_exact` and A22 theorems are not in this partition. Only their `#check`/`#print axioms` driver is. So the "unrestricted eta, no added hHC" condition can be checked only for the parts that are here. Integration must confirm it at the top level.

## 1. File inventory

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46DR6Incidence.lean | Inspected |
| 2 | ActualBinaryMatrixHC46DR6Mobius.lean | Inspected |
| 3 | ActualBinaryMatrixHC46DR6Moment.lean | Inspected |
| 4 | ActualBinaryMatrixHC46DR6SignMoments.lean | Inspected |
| 5 | ActualBinaryMatrixHC46FourierA16.lean | Inspected |
| 6 | ActualBinaryMatrixHC46OriginalExactInhabitantChecks.lean | Inspected (driver only; the theorems it checks are in another partition) |
| 7 | ActualBinaryMatrixHC46RealQNorm.lean | Inspected |
| 8 | ActualBinaryMatrixHC46RealQNormChecks.lean | Inspected |
| 9 | ActualBinaryMatrixHC46RealQTransport.lean | Inspected |
| 10 | ActualBinaryMatrixHC46RealQTransportChecks.lean | Inspected |
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

No file and no proof body was skipped.

## 2. Checks on the main results

**DR6 final theorem (`DR6Moment.dr6_actual_complex_fourth_moment_over_162_le`)**
- **Premises:** the only premise is `ComplexFourierSupportedThrough D f`. There is no rank guard, no scalar-F2 premise, no reality or Booleanity assumption, and no hHC premise.
- **Not vacuous:** the premise is satisfiable, for example by constant functions or `f = 0`. All values of `n`, `d` and `D` are covered.
- **D = 0:** handled separately. Support 0 forces `f` to be constant, so E|f|⁴ = |c|⁴ ≤ RHS.
- **D ≥ 1 arithmetic:** the bound E|f|⁴ ≤ 2a + 2·(31/225)·S, divided by 162, is ≤ a + S. This is correct and loose.
- **Direction:** the F2 bridge `dr6_actual_complex_f2_remainder_eq_signedCoefficient` is an exact identity. The grid-to-full step (`dr6_actual_weighted_filter_energy_atMostD_le_full`) is an injection with nonnegative extra terms, so it enlarges the right-hand side and is valid.
- **Right-hand side scope:** S is the unrestricted sum over all (A,B) ≠ (0, whole). Matching it to the manuscript's own statement is left to integration (question 3 below).

**F1 bound (`dr6_actual_f1_total_energy_le`): 2^(6D²)**
- The outer predecessor count is 2^(rank X²) ≤ 2^(4D²), using rank X ≤ 2D.
- The coefficient mass is ≤ 2^(D²)·E|f|², which is squared, giving 2^(2D²).
- The total exponent is 4D² + 2D² = 6D². Correct.
- Outputs with rank > 2D are shown to contribute zero.
- The map (X, p) ↦ (A, B) is injective because X = A + B, so the global Frobenius bound is applied only once.

**F2 bound (`DR6Incidence`): exponents 7D and the 31/225 factor**
- **Signed weight:** α_k² = 2^(2⌊k(k−1)/2⌋) ≤ 2^(Dk), which needs k ≤ D. That condition is imposed (`dr6_mobiusAlpha_sq_le_pow`).
- **Mixed term:** the weight satisfies ≤ 2^(D(i+j)).
- **Carrier count:** ≤ 2^(rank X·(i+j)) ≤ 2^(2D(i+j)). This gives 3D per grade.
- **Weighted Cauchy:** contributes 4D more, for 7D in total.
- **31/225 factor:** sum over grades (i,j) ≠ (0,0) of 2^(−4D(i+j)) ≤ (16/15)² − 1 = 31/225. This needs q ≤ 1/16, which follows from D ≥ 1, and D ≥ 1 is a hypothesis.
- **Grades above D:** these are removed by exact zeros (`dr6_complexFilter_eq_zero_of_grade_gt_support`), not by assumption.
- **Möbius identity:** the signed-incidence identity is exact (`dr6_f2_a5SquareCoefficient_eq_original_obstruction_sum`). Absolute values are taken only after the cancellation.

**Real-q / A22 pieces (`RealQNorm`, `RealQTransport`)**
- `pConjugate p = p/(p−1)` is not rounded to an integer. Hölder is proved with the normalisation cancelled exactly, and it requires `Nonempty X`.
- `exactPR_to_actual_LqGlobal` has premises `2 ≤ p` and `PseudorandomExact r eta b` only, with no cap on eta. The cap at 1 comes from the Boolean density. The direction is correct: the fibre energy is ≤ min(eta, 1), and raising both sides to 1/q = 1 − 1/p preserves the inequality.
- If eta < 0, the hypothesis appears to be unsatisfiable: fibres always contain their base and energy is ≥ 0. This assumes `exactPR_to_actual_normSqGlobal` bounds the energy by eta, which is a cross-partition item. If so, the "arbitrary eta" claim is true but only says something when eta ≥ 0.
- The order-zero (whole-space) fibre is included, so `UpToActualLqGlobal_parameter_nonneg` is derived rather than assumed.

## 3. Findings

| ID | Severity | Where | Finding |
|---|---|---|---|
| N1 | Low (status text) | `DR6Moment` module docstring | It says the final inequality "is authored source only and remains uncompiled and uncertified". This contradicts the GCP receipt (seven zero exits, 319-file closure). Integration must confirm `DR6Moment` is inside the certified closure and treat this text as out of date; if it is not inside, the DR6 claim has no support. |
| N2 | Low (stale, under-claims) | `DR6Incidence` module docstring; `dr6_f2_a5_global_XGradeEnergy_bound` docstring; `DR6Moment.dr6_actual_fourth_moment_le_f1_plus_f2` docstring; `DR6Mobius` header ("neither milestone proves the signed A5 incidence reindexing") | They describe the global carrier enlargement and the F2 discharge as still open. Later code in the same files does both (`dr6_f2_a5_global_fixed_D_ambient_bound`, `dr6_actual_complex_fourth_moment_over_162_le`). No over-claim, but the stated scope does not match the code. |
| N3 | Info | `DR6Incidence`, the bare `end` just before `dr6_f2_a5_global_fixed_D_ambient_bound` | The `end` closes the `noncomputable section`, so the last theorem sits outside the section and its local instance attributes. The receipt says it compiles. Cosmetic only. |
| N4 | Info | `DR6Moment.dr6_actual_complex_f2_remainder_eq_signedCoefficient` | Has an unused implicit `{D}`, supplied explicitly at the call site. Harmless. |
| N5 | Info (do not cite as selector-specific) | `T2Transfer.t2_right_complement_energy` | The `t2RightSelected` hypothesis is bound to `_hcan` and never used. The conclusion (one nonnegative term ≤ the full sum) holds for every (C,H). It must not be cited as a T2-specific energy fact. |
| N6 | Info | `RealQTransport.carrierFibreQNorm_hyperplane_coordinate` | The docstring says "Adapted line coordinates"; it should say hyperplane (copy-paste error). |
| N7 | Note (conditional; outside milestone) | `ChangedAmbient8SBoundary.AllAmbientInverse`, `first_inverse_witness_of_eightS` | `AllAmbientInverse` is a Prop taken as a premise. Nothing proves it, so the theorem is conditional only. For some parameter choices, such as S ≤ 0, the premise may be unsatisfiable, which would make the theorem vacuous there. This is consistent with robust8S remaining open, but it must not count as discharged. |
| N8 | Note (conditional) | `FixedFunctionalMatrixLift.failed_zoom_gives_*`, `LeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom` | Each assumes `hfail` (every budget-r zoom has agreement ≤ e) and `r < d`. They are legitimate contrapositive steps but remain conditional. |
| N9 | Info | `FixedFunctionalStarMoment` | Uses `set_option backward.isDefEq.respectTransparency false`. This changes elaboration only; the kernel still checks the result. Worth recording for reviewers. |
| N10 | Info (provenance) | `MaximalPairLadder` header comment | It embeds an older GCP receipt (commit d93d23b, 3058/3059 jobs). That is not evidence for this milestone and should not be relied on. |
| N11 | Info | `MaximalPairLadder.maximalPairLadder` | Assumes `4*B ≤ agreement` but uses only `B ≤ agreement`. The stated theorem is weaker than it could be, which is harmless. |

There are no Critical, High or Medium findings. Nothing found shows a false claim, a vacuous main result, a reversed inequality, or a hidden extra premise among the declarations in this partition.

## 4. Questions for integration

1. **Top-level statements.** Confirm the statements of `original_HC46_exact` (driven from partition-6 Checks) and of the A22 consumer: eta unrestricted, no added hHC premise, and the same selected consumer. Also confirm which DR6 statement the consumer actually uses, and that its real-q exponent is `pConjugate p`.
2. **Definitions this partition relies on.** These are defined in other partitions; check each against the manuscript:
   - **DR6 combinatorics:**
     - `DR6F2Obstruction`, `DR6F1Witness`, `dr6_matrix_f1_or_f2_coverage`, `DR6DirectYDecomposition` and `dr6_y_decomposition_card_le_pow` (Convolution).
     - `DR6OrdinarySelected` (A17).
     - `complex_fourier_parseval`, including its normalisation (A12).
     - `W6Grass`, `w6_card_grass` and `w6_card_grass_mul` (A7).
   - **Pseudorandomness and affine restrictions:**
     - `PseudorandomExact` and `exactPR_to_actual_normSqGlobal`.
     - `actualOfRaw`, `rawOfActual`, `liftRestriction` and `transposeRaw`, plus their budget/order equalities.
   - **Selectors and derivatives:**
     - `Selected`, `actualW6Derivative_carrier_fourierCoeff` and `typedW6QComponent`.
     - `mixedCoordinatePeel_rankProjection_eq_derivativeChain`.
     - `typed_A14_fixedLine` and `typed_A14_fixedHyperplane`.
   - **Zoom and star laws:**
     - `ExactBudgetZoomBound` and `exact_zoom_implies_nominal_pseudorandom`.
     - `starLaw_atom`, `matchingStarMass` and `grassmannExperiment`.
3. **Manuscript constants.** Check 1/162, 2^(6D²), 2^(7D(i+j)), the exclusion of (0, whole) from S, and 31/225 against submission-manuscript.md (lines 1385–1386 and 1584–1613). This partition does not include the manuscript.
4. **External libraries.** Init, Mathlib and Batteries are trusted at their pinned versions, as stated. They were not reviewed here.
5. **Hashes.** Compare the per-file SHA256 values against `source-index.json`; I could not do this.
6. **Out of scope and still open.** Spectral47; the source/star/robust8S, numericNO, encoded reduction, runtime and learning gates; upstream bridges; and the manuscript/render/novelty gates. Nothing in this partition, including N7 and N8, discharges any of them.
