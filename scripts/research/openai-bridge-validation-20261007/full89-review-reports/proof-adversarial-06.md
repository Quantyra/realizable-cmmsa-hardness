# Partition 6/9 review: Full89 original A22/HC46 selected-consumer milestone

**Verdict: GO-WITH-NOTES.** This verdict covers partition 6 only. It is not a verdict on the whole campaign.

I read the 21 complete files in this packet and nothing else. I used no tools: I did not open the source index, did not run Lean or Lake, and wrote nothing. I took the compile, axiom and trace facts from your scope statement and did not check them myself. Each `#print axioms` output in the Checks files is part of that scope statement; I did not see the outputs. I give locations as declaration names plus position in the file. I did not count line numbers.

## Files inspected

All 21 files were inspected in full. None was skipped.

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46DR6Incidence.lean | inspected |
| 2 | ActualBinaryMatrixHC46DR6Mobius.lean | inspected |
| 3 | ActualBinaryMatrixHC46DR6Moment.lean | inspected |
| 4 | ActualBinaryMatrixHC46DR6SignMoments.lean | inspected |
| 5 | ActualBinaryMatrixHC46FourierA16.lean | inspected |
| 6 | ActualBinaryMatrixHC46OriginalExactInhabitantChecks.lean | inspected (only `#check` and `#print axioms` lines) |
| 7 | ActualBinaryMatrixHC46RealQNorm.lean | inspected |
| 8 | ActualBinaryMatrixHC46RealQNormChecks.lean | inspected |
| 9 | ActualBinaryMatrixHC46RealQTransport.lean | inspected |
| 10 | ActualBinaryMatrixHC46RealQTransportChecks.lean | inspected |
| 11 | ActualBinaryMatrixHC46T2Transfer.lean | inspected |
| 12 | ActualBinaryMatrixHC46TypedA14Energy.lean | inspected |
| 13 | ActualBinaryMatrixHC46TypedFourierTransport.lean | inspected |
| 14 | ActualChangedAmbient8SBoundary.lean | inspected |
| 15 | ActualFiniteDegreeFourierProduct.lean | inspected |
| 16 | ActualFiniteDegreeFourierReconstruction.lean | inspected |
| 17 | ActualFixedFunctionalMatrixLift.lean | inspected |
| 18 | ActualFixedFunctionalStarMoment.lean | inspected |
| 19 | ActualLeafLabelRankImageAlignment.lean | inspected |
| 20 | ActualMZ24HyperplaneSupport.lean | inspected |
| 21 | ActualMaximalPairLadder.lean | inspected |

## Core audit: the final DR6 theorem

The theorem is `dr6_actual_complex_fourth_moment_over_162_le` (Moment, last declaration).

**Hypotheses.** It takes only an arbitrary complex `f` and `hsupport : ComplexFourierSupportedThrough D f`. There is no hHC premise, no reality or Boolean assumption, no rank guard on X, and no assumed bound on the F2 term. `D` can be any natural number, and the case `D = 0` is proved separately.

**Not vacuous.** The hypotheses can be satisfied. The right-hand side is not trivially large: the pair (A,B) = (0, whole) is excluded, and it is the only pair that selects Y = 0, so the weighted sum does not trivially dominate E|f|⁴.

**Direction.** Each step is an upper bound in the right direction:
- E|f|⁴ = Σ_X |(f̂∗f̂)(X)|² (Parseval).
- That is ≤ 2·F1 + 2·F2 (split into the F1 complement and the F2 remainder, then (a+b)² ≤ 2a² + 2b²).
- F1 ≤ 2^{6D²}‖f‖₂⁴.
- F2 ≤ (31/225)·S.
- Dividing by 162 gives (2a + (62/225)S)/162 ≤ a + S. This is a lot of slack, but it is valid.

**Exponent checks, recomputed by hand:**
- **Cauchy weights:** c = 2^{2D(i+j)}, and Σ over (i,j) ≠ (0,0) of 2^{−4D(i+j)} ≤ (16/15)² − 1 = 31/225. This needs D ≥ 1 (so q ≤ 1/16), which is enforced.
- **Möbius weight:** α_k² = 2^{k(k−1)} ≤ 2^{Dk} needs k − 1 ≤ D. Here k ≤ D is enforced, and the grades with k > D are separately shown to be exactly zero by the support hypothesis.
- **Carrier count:** at most 2^{rank X·(i+j)} ≤ 2^{2D(i+j)}. The case rank X > 2D is separately shown to give a zero coefficient.
- **Total weight:** 2^{4D(i+j)} · 2^{D(i+j)} · 2^{2D(i+j)} = 2^{7D(i+j)}. ✓
- **F1:** 2^{4D²} (outer predecessors when rank X ≤ 2D) × (2^{D²})² (coefficient mass) = 2^{6D²}. ✓

**Incidence identity.** The signed weights are α_i, α_j and −α_iα_j. Multiplied by the actual Grassmannian counts, they combine to S_I + S_J − S_I·S_J, which is the indicator of the union. The Möbius indicator Σ_k [n choose k]₂·α_k = 1_{n>0} follows from the q-binomial product Π(1 − 2^i), which vanishes for n > 0. The kernel side is moved to the image side through coordinate duality, as an actual bijection rather than a Gaussian proxy.

**Moving from the per-X carrier to the global sum.** Three proved steps, each in the right direction:
1. Enlarging to the ambient carrier only adds nonnegative energy.
2. Restricting to grades ≤ D drops only terms that are exactly zero.
3. The injection into the nonzero (A,B) pairs keeps the weight unchanged, because the dimensions recover the grade.

## Other files in the selected-consumer path

**Real-q A22 support (RealQNorm, RealQTransport).**
- `pConjugate p = p/(p−1)` is the exact real conjugate with no rounding, and `pConjugate_holder` requires 2 ≤ p.
- Hölder, Minkowski and homogeneity each carry explicit hypotheses: q > 0, q ≥ 1, or a Hölder-conjugate pair.
- `UpToActualLqGlobal` always includes the order-zero whole-space restriction, so it is not vacuous (see `UpToActualLqGlobal_parameter_nonneg`).
- `exactPR_to_actual_LqGlobal` accepts any eta and caps it with `min eta 1`. For eta ≥ 1 the bound is trivially 1. For eta < 0 the premise cannot hold, because fibre energy is nonnegative. This is honest handling of an unrestricted eta.

**HC46 support.** The DR6 chain above is the HC46 input in this partition. No hHC premise appears anywhere in the partition.

## Findings

No finding is blocking.

**Findings 1–3 are stale documentation (low severity).** In each case the comment says the work is incomplete or uncertified when it is not:
1. **Moment, module docstring:** says the inequality "is authored source only and remains uncompiled and uncertified." That conflicts with the scope statement's seven zero exits. The docstring on `dr6_actual_fourth_moment_le_f1_plus_f2` still says a separate Möbius theorem must discharge F2, but F2 is discharged in the same file.
2. **Incidence, module docstring and `dr6_f2_a5_global_XGradeEnergy_bound`:** say "global X-carrier enlargement and final F2 combination remain open." Both are proved later in the same file: `dr6_f2_a5_XGradeEnergy_le_fixed_D_ambient` and `dr6_f2_a5_global_fixed_D_ambient_bound`.
3. **Mobius docstring** ("Neither milestone proves the signed A5 incidence…") and the **MaximalPairLadder header** (GCP receipt at d93d23b, Lean 4.34.0-rc2) both look stale against the current certification. I cannot check either one.

**Finding 4 (low): `t2_right_complement_energy` (T2Transfer) never uses its main hypothesis.** The `h : t2RightSelected …` premise only feeds an unused `_hcan`. The conclusion (one nonnegative term ≤ the full sum) is true for any (C,H). Do not cite it as evidence of T2 energy accounting.

**Finding 5 (info): `maximalPairLadder` asks for more than it uses.** It assumes `4*B ≤ agreement` but only uses `B ≤ agreement`. This is sound but has unused slack. Integration should check that no consumer reads a factor of 4 into the conclusion.

**Finding 6 (info): `first_inverse_witness_of_eightS` (ChangedAmbient8SBoundary) is conditional.** It depends on the hypothesis `AllAmbientInverse`, a Prop that is defined but never proved. The theorem itself is only the step 8S ≤ density ⇒ S ≤ density. It is not a universal claim, and the robust 8S work stays open.

**Finding 7 (info): failed-zoom lemmas are conditional.** `failed_zoom_gives_*` and `actual_leaf_failed_zoom_gives_nominal_pseudorandom` depend on `hfail`. They run in the contrapositive direction (decoding failure implies pseudorandom), which is correct.

**Finding 8 (info): small items with no soundness effect.**
- Moment: the implicit `{D}` in `dr6_actual_complex_f2_remainder_eq_signedCoefficient` is unused.
- Incidence: `hKB` in `dr6_kernelSuperspace_annihilator_dim` is unused.
- Incidence: `dr6_f2_signed_weight_endpoints` holds by `rfl`.
- Incidence: `dr6_f2_gradeGrid_weighted_cauchy` and the private D×D first-factor lemma sit outside the final chain.
- Incidence: the last theorem comes after the `end` that closes the noncomputable section, so it runs without the section's local instances. The scope statement says this compiled.
- StarMoment sets `backward.isDefEq.respectTransparency false`, a nonstandard elaboration option. The kernel recheck still applies.

## Questions left open for integration

1. **Convolution file definitions.** I could not check `DR6F2Obstruction`, `DR6F1Witness`, `dr6_matrix_f1_or_f2_coverage`, `DR6DirectYDecomposition` or `dr6_y_decomposition_card_le_pow`. The F1/F2 split depends on these.
2. **Filter bridge.** The DR6 right-hand side uses `DR6ComplexOrdinaryFilter`, defined in Incidence. Only the selector is shown equivalent to `DR6OrdinarySelected` (A17). Confirm the HC46 consumer uses this filter or bridges the filters too.
3. **Normalizations defined elsewhere.**
   - From A7: `W6Grass`, `w6_card_grass`, `w6_card_grass_mul`, `w6FrameProduct`.
   - From A12: `complex_fourier_parseval`.
   - From BinaryMatrixFourier: `lpNorm`/`lpMoment`, used by `realQNorm_nat_eq_lpNorm`.
4. **Selected consumer statements.** I did not see the statement of `original_HC46_exact` or of the A22 theorem. Confirm they consume `dr6_actual_complex_fourth_moment_over_162_le` and `exactPR_to_actual_LqGlobal` with q = `pConjugate p`, and that no hHC premise is added.
5. **Pseudorandomness and zoom bridges.** I did not see `PseudorandomExact`, `exactPR_to_actual_normSqGlobal`, `fibreEnergy`, `ActualAffineRestriction.order`, `exact_zoom_implies_nominal_pseudorandom` or `ExactBudgetZoomBound`.
6. **`AllAmbientInverse`.** Confirm no one of the 172 roots is counted as having discharged it.
7. **Manuscript constants.** The constants 162, 31/225, 7D(i+j) and 6D², and the manuscript lines 1385–1386 and 1584–1613, were not checked against the manuscript. The manuscript and render gates stay open.
8. **External library trust.** Trust in Init, Mathlib and Batteries is explicit and was not reviewed here. That includes Hölder/Minkowski (`Real.inner_le_Lp_mul_Lq_of_nonneg`, `Real.Lp_add_le_of_nonneg`), the `Subspace` dual-annihilator lemmas and `isSimpleModule_iff_finrank_eq_one`.

Still open, as you stated: the broader Spectral47; the source/star/robust8S/numericNO/encoded-reduction/runtime/learning work; upstream bridges; and the manuscript, render and novelty gates.
