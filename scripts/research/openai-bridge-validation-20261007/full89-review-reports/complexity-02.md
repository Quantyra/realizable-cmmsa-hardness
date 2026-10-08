# Complexity review: Full89, partition 2/9

**Scope.** I reviewed only the 18 complete files pasted into this prompt. I did not run any tools, write anything or start subagents. I did not open the source index or recompute SHA-256 values, so I have not checked that this text matches the indexed sources. I did not re-run the native-build evidence (the seven zero exits, 172 standard axiom profiles and 319-file source closure); I take it as stated. Library trust in Init, Mathlib and Batteries is taken as given, not reviewed here. This verdict covers this partition only and is not a judgement on the whole campaign.

**Verdict: GO-WITH-NOTES** for this partition. I found no blocking defect. Every supplied file body was inspected; nothing was skipped. Questions that depend on other partitions are listed in §4.

## 1. File inventory

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46A18OriginalGlobalInduction.lean | Inspected in full |
| 2 | ActualBinaryMatrixHC46A18QuotientSamplingLaw.lean | Inspected in full |
| 3 | ActualBinaryMatrixHC46A18SourceConditioning.lean | Inspected in full |
| 4 | ActualBinaryMatrixHC46A18SourceGlobal.lean | Inspected in full |
| 5 | ActualBinaryMatrixHC46A18TransposeAverage.lean | Inspected in full |
| 6 | ActualBinaryMatrixHC46A18TransposeTransport.lean | Inspected in full |
| 7 | ActualBinaryMatrixHC46A20SquareGlobalness.lean | Inspected in full |
| 8 | ActualBinaryMatrixHC46A20SquareSupport.lean | Inspected in full |
| 9 | ActualBinaryMatrixHC46A21DyadicMoment.lean | Inspected in full |
| 10 | ActualBinaryMatrixHC46A22OperatorLq.lean | Inspected in full |
| 11 | ActualBinaryMatrixHC46A22OperatorLqChecks.lean | Inspected in full (only `#check` / `#print axioms`) |
| 12 | ActualBinaryMatrixHC46A22OriginalInductionChecks.lean | Inspected in full (only `#check` / `#print axioms`) |
| 13 | ActualBinaryMatrixHC46A22ParentFactorizationChecks.lean | Inspected in full (only `#check` / `#print axioms`) |
| 14 | ActualBinaryMatrixHC46A6Transfer.lean | Inspected in full |
| 15 | ActualBinaryMatrixHC46A7CarrierParseval.lean | Inspected in full |
| 16 | ActualBinaryMatrixHC46A7EnergyConsumer.lean | Inspected in full |
| 17 | ActualBinaryMatrixHC46A7HybridW6Transport.lean | Inspected in full |
| 18 | ActualBinaryMatrixHC46A7PredecessorCount.lean | Inspected in full |

## 2. Audit of the main chain

### Assumptions, quantifiers and the size parameter (eps/η)
- **`actual_A18_original_global`** is universal over n, d, D, r, eps and f. It assumes only `ComplexFourierSupportedThrough D f` and `OriginalActualInfluenceThrough D eps f`.
  - The influence premise is a mean over the whole carrier for every A, B, T with cost ≤ D. It is not a conditional mean over a fibre.
  - The proof inducts internally on both D and r. It assumes no recursive globalness and no hHC premise.
- **The size parameter is unrestricted.** Its nonnegativity is always proved, never assumed:
  - A18: `original_influence_parameter_nonneg`
  - SourceGlobal: `actual_source_parameter_nonneg`
  - A20: `filteredCarrierFunction_parameter_nonneg`
  - A21: same lemma (`heps`)
  - A22: `UpToActualLqGlobal_parameter_nonneg`
- **Vacuity.** The premises are satisfiable by non-trivial inputs, e.g. a constant f = c with eps ≥ |c|². The conclusions are non-trivial when eps is small.
  - The SourceGlobal expanded-branch lemmas need `v` with `phi v = 1` and a strict extension `B'`, so they become vacuous when the domain subspace is ⊥ or the codomain subspace is ⊤. This is correct conditional behaviour, not a defect.
  - The case s = 0 in `actual_expanded_outside_column_energy_le_two` is likewise an inconsistent-hypothesis branch, closed by `omega`. Fine.
- **Direction of the chain.** A16 turns globalness into influence (`a20_three_degree_global`, which ignores the cost hypothesis `_hcost`). A18 turns influence into globalness at order 3D. A19 and A20 give globalness of the square at 2D. A21 does the dyadic induction. There is no circularity.
- **Real-q A22.** All Lq lemmas take `1 ≤ q` for real q (q need not be an integer) and keep every affine fibre.
- **Dyadic restriction.** A21 is stated only for dyadic p ≥ 2. Its docstring says so accurately.

### Exponent bounds, re-derived by hand
- **A18 budget.** From `hpow` and `hscale`, `a18BudgetScale D r eps = 2^(10Dr)·eps` (inferred: the definition itself is external).
  - The top term needs 2·2^(10(D−1)(r−1)−10Dr) + 4·2^(2D−10D) ≤ 2^(−10) + 2^(−6) = 9/512 for D, r ≥ 1. This matches `a18_top_contribution_le_nine512` exactly.
  - The lower terms need (Σ_{i<D} 2^(5ir))² ≤ 2^(10Dr)/4. This holds with a wide margin, roughly 2^(10(D−1)r)·1.07 against 2^(10Dr−2).
  - Base cases: D = 0 (constant function, budget = eps) and r = 0 (the whole space) are correct.
- **A20 three-degree budget.** 30D² + 11D² = 41D². Then 114 + 41 + 41 = 196, giving 2^(196D²)·eps². ✓
- **A21 recurrence.** With a(p) = 200p² − 100p, a(2q) − 4a(q) = 200q ≥ 114 + 196(q/2 − 1) = 98q − 82. ✓
  - The eps exponent works out to 1 + 2(q/2 − 1) = q − 1 = (2q)/2 − 1. ✓
  - Base cases p = 2 and p = 4 (with a(4) = 2800 ≥ 114) are correct.
- **A22 loss.** (1 + 2^j)(1 + 2^(j−1)) ≤ 2^(2j+1) ≤ 2^(3j) for j ≥ 1. ✓
- **A6.** The fourth-power Hölder cost is N³ with N = 2^(ij), i.e. 2^(3ij). Then 7D(i+j) + 3ij ≤ 10D(i+j) ≤ 20Dt ≤ 24Dt. ✓
- **W6 weighted sum (67/63).**
  - Rank-k predecessor count ≤ 4·2^(2k(j−k)), using the Gaussian bound with normalized frame product ≥ 1/4, which is proved correctly.
  - Each term with k ≥ 1 is ≤ 4·2^(−6k²) ≤ 4/64^k. With the k = 0 term equal to 1, the total is 1 + 4/63 = 67/63. ✓
  - The predecessor/successor swap in `actualW6Derivative_weighted_fourth_moment_le_67_63` is oriented consistently with `W6RankKPredecessor`.

### Conditional facts versus universal claims
- **SourceConditioning:** the half-mass event is derived from the binary codimension-1 geometry; it is not assumed.
- **QuotientSamplingLaw:** coordinate bijections only. It makes no energy claim, as its own header states.
- **TransposeTransport:** explicitly does not identify the hyperplane draw with the line draw.
- **A6:** `manuscript_A6` is a universal inequality. The fact that mixed orders above D contribute zero is a separate lemma (`a6_mixed_zero_of_order_gt`) and is not built into the statement.

## 3. Findings

None of these blocks the verdict.

| ID | Severity | Location | Finding |
|---|---|---|---|
| N1 | Low | A20SquareGlobalness, `set_option backward.isDefEq.respectTransparency false in` before `manuscript_A20_raw_fourth_le` | A non-default elaborator option. The kernel still re-checks the proof and the axiom profile is reported as standard. Record it as a trust-surface note. |
| N2 | Info | A20SquareSupport (`maxHeartbeats 1200000`), A6Transfer (`1500000`) | Raised elaboration budgets. Not a soundness issue. |
| N3 | Info | A6Transfer, `manuscript_A6` | The weighted sum keeps terms with order > D; the docstring's "orders above the degree contribute zero" relies on a separate, unused lemma. `a6_reconstruct_forward/backward` are also standalone. Any downstream consumer must apply the truncation itself. |
| N4 | Info | HybridW6Transport, `typedW6OutputEnergy` docstring | Says "fourth-energy base" but defines a second moment. `typedW6OutputFourth` is the fourth moment. Docs only. |
| N5 | Info | SourceGlobal, `actual_source_quotient_coset_mean_le_two` statement (`  let qdom` under-indented); QuotientSamplingLaw, ` theorem quotientSectionCoordinates_of_kernel_line` (leading space) | Cosmetic; reported to compile. |
| N6 | Info | SourceGlobal: `hQorder` unused in `actual_expanded_outside_column_energy_le_two`, `hpartsEq` unused in both `_coords_coe` lemmas | Harmless leftover hypotheses. |
| N7 | Info | `attribute [local instance] Fintype.ofFinite`, used in many files | Possible instance overlap. `Fintype` is a subsingleton, so this is sound; mentioned for maintainability. |
| N8 | Info | A18SourceGlobal / Conditioning / QuotientSamplingLaw | `actual_A18_original_global` does not use this route; that proof goes through A17. The route's energy consumer (FullFunctionalEnergy) is outside this partition. |

## 4. Questions for integration (other partitions or external boundaries)

1. **External statements this partition relies on, to be checked against their own partitions:**
   - `actual_A17_full_parent_energy`
   - `a18_top_contribution_le_nine512`, `a18_lower_absorption`, `a18_uniformL2_finset_sum_le`, and the definition of `a18BudgetScale` (which I inferred as 2^(10Dr)·eps)
   - `actualDerivativeCoordinate_support_drop`, `actual_derivative_rank_projection_energy_le`
   - `typed_line_A1_operator_step`, `typed_hyperplane_A1_operator_step`, `manuscript_A1_complex`
2. **A16 and A19 constants:** confirm that `filteredCarrierFunction_energy_le_A16` really holds for every carrier with no cost bound, at 2^(11D²), and that `manuscript_A19_actual` has the constant 2^(114D²).
3. **A6 inputs:** `dr6_actual_complex_fourth_moment_over_162_le` and the weight definition of `dr6ActualWeightedOrdinaryFilterEnergy`, plus `t1Triple_card` = 2^(ij) and `w6_actual_predecessor_frequency_fiber_card`.
4. **Real-q and raw/actual transport lemmas:** `realQNorm_add_le`, `UpToActualLqGlobal_translate/transpose/rawLastColumn/rawLastRow/parameter_nonneg`; `raw_implies_actual`, `actual_implies_raw`, `transpose_raw`.
5. **Original A22 itself:** this partition contains only the `#check` files for `manuscript_A22_actual` and the ParentFactorization lemmas. The partition that holds their bodies must confirm they use the A22OperatorLq lemmas with real q and the same selected consumer, and add no hHC premise.
6. **Which theorem is the "selected consumer":** this partition contains the A7/W6 and A6 consumers, but the consumer's root statement is not here.
7. **Other open gates:** Spectral47, source/star/robust8S/numericNO, encoded reduction, runtime, learning, upstream bridges, and the manuscript/render/novelty gates remain open and are outside this partition.
