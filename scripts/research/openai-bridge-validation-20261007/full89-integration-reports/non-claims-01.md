# Full89 integration, window 1/3 (contracts and selected consumer): independent non-claims review

## Verdict for this window: GO-WITH-NOTES. The overall integration remains INCOMPLETE.

This verdict covers only the 13 complete bodies supplied in this window. It is not a milestone acceptance and not a full-manuscript verdict.

- Every packet-7, -8 and -9 HIGH or Medium question that these 13 bodies can settle is resolved or bounded below.
- Questions that depend on bodies outside this window stay open for windows 2 and 3: A7–A12, A14–A18, A20, A21, DR6, BooleanGlobalness and the MatrixLift substrate.
- I used no tools, ran no Lean or Lake, and did not recompute any SHA256. File identity rests on the supplied pins and qualified receipts.
- I cite by declaration name. Without a line counter I give no line numbers.

## Bodies covered: 13 supplied, 13 inspected, 0 skipped

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46A22ParentFactorization (A30B…DF7A) | Inspected in full |
| 2 | ActualBinaryMatrixHC46A22OriginalInduction (B044…9BCA) | Inspected in full |
| 3 | ActualBinaryMatrixHC46OriginalExactInhabitant (6F56…6C95) | Inspected in full |
| 4 | ActualSelectedComplementHC46OriginalApplication (104A…B5B0) | Inspected in full |
| 5 | ActualSelectedComplementAnalyticMoment (BFAE…92F9) | Inspected in full |
| 6 | BinaryMatrixFourier (8103…70D8) | Inspected in full |
| 7 | ActualBinaryMatrixHC46 (1C47…662C) | Inspected in full |
| 8 | ActualBinaryMatrixHC46RealQNorm (FEB1…8C01) | Inspected in full |
| 9 | ActualBinaryMatrixHC46RealQTransport (3093…1B14) | Inspected in full |
| 10 | ActualLeafLabelRankImageAlignment (5991…80C2) | Inspected in full |
| 11 | ActualFixedFunctionalMatrixLift (1002…2E07? no: 1002…893…, pin 1002E7F8…22BF90B6851A270614ED…; as supplied 1002…2E07 is DirectComparison) | Inspected in full |
| 12 | MatrixLiftNominalDirectComparison (E8C4…2E07) | Inspected in full |
| 13 | MatrixLiftExactBudgetZoom (4193…DD32) | Inspected in full |

Correction to row 11: the FixedFunctionalMatrixLift pin as supplied is `1002E7F8541C8FDE977E0123FB7CBFA85C33D6CF0D2593D5925929E2FC22147F`.

The other 157 of the 170 selected bodies are not in this window. For them I reuse only the prior three-lens reports, tied to their unchanged pinned identities. I did not re-inspect them.

## 1. Universal HC46 and the selected consumer

### `original_HC46_exact : HC46ExactContract`
- **The contract is the unchanged definition.** The proof's type is literally the `HC46ExactContract` constant defined in `ActualSelectedComplementAnalyticMoment`. That definition quantifies over all `n d h r i p` and every real `eta`. Its only premises are `d = 2h`, `PseudorandomExact r eta b`, `i ≤ r`, `4 ≤ p` and dyadic `p`.
- **It takes no hHC, Spectral, `eta ≤ 1` or basis-invariance premise.** In the body, `hEven` reaches only the rank-zero branch, which ignores it (`_hEven`). The proved statement is therefore stronger than the contract: d does not need to be even.
- **The `i = 0` branch** goes through `hc46_rank_zero_exact`. That covers `eta ≤ 1` via `binary_hc_rankZero_exact`, and `eta > 1` via mean ≤ 1 ≤ `eta^α`.
- **The `i ≥ 1` branch:**
  - `0 ≤ eta` is derived from `boolean_mean_le_of_exact`.
  - It sets `delta = min eta 1`. The case `delta = 0` forces `b ≡ false`, so the norm is 0.
  - `exactPR_to_actual_LqGlobal` gives globalness with parameter `(min eta 1)^(1-1/p)`. That is definitionally the parameter in `hLqi`, which answers packet-1 proof-adversarial Q1. It is restricted to order `i` through `hi`.
  - The chain is `manuscript_A22_actual`, then `actual_A18_original_global` (scale `2^(10i²)`), then `manuscript_A21_actual`.
  - I re-derived the arithmetic by hand:
    - The delta exponent is `1 + 2(1-1/p)(p/2-1) = p - 2 + 2/p`, which is at least `p - 2`.
    - Because `delta ≤ 1`, `rpow_le_rpow_of_exponent_ge` is applied in the correct direction.
    - The coefficient satisfies `200i²p² + (10i² + 500i²p)·m ≤ 455i²p² ≤ 500i²p²`.
    - Taking the 1/p root gives `2^(500i²p)·delta^((p-2)/p)`, and `delta ≤ eta` with an exponent ≥ 0 finishes it.

### The selected wrapper
- `selected_leaf_HC46_original` passes `original_HC46_exact` as `hHC` to `selected_leaf_HC46_of_exact_PR`. That theorem's body is a single application of `hHC` at `rankImageBoolean (leafMatchBit T f)`, with `hEven := rfl` and `d = 2*h`.
- `selected_leaf_failed_zoom_HC46_original` composes this with `selected_leaf_failed_zoom_PR` on the same predrawn `T` and `f`:
  - `actual_leaf_failed_zoom_gives_nominal_pseudorandom` rewrites through `leafMatchBit_fun_eq_matchingLeafSet`;
  - `failed_zoom_gives_nominal_pseudorandom`, `failed_zoom_gives_exact_bound` and `exact_zoom_implies_nominal_pseudorandom` follow.
  - The output parameter is `eta = 2e`.
- **Native evidence:** all four focused consumers have standard profiles `[propext, Classical.choice, Quot.sound]` in the fresh172 stdout, with no `sorryAx`.

### Can the universal theorem serve as `hHC` in the same material-moment consumer?
- **Logically, yes.** `selected_actual_material_moment_bound` takes `(hHC : HC46ExactContract)`, the same closed Prop with no universe parameters. Supplying `original_HC46_exact` there type-checks by constant identity. Inside the consumer, the contract is used only at `b = selectedF Tc fc`, with `hPR` derived from `hfail` on the same `Tc` and `fc`.
- **No hHC-free material export exists.** One cannot be written in `AnalyticMoment` itself, because `OriginalExactInhabitant` imports `AnalyticMoment`. No downstream wrapper exists in the supplied sources, and none is a requested native root.
- **The material bound is outside the native evidence.** Its axiom profile is not in the stdout, and it is not reached by the four focused consumers. That fits the pin `ActualSelectedComplementAppendMoment: transitively_consumed false`.
- **Its imported support modules appear not to be in the 170 selected paths**, by my reading of the supplied list: `ActualSelectedSpectralParameters`, `ActualRankImageRightBasisInvariance`, `ActualAppendFourierCrossLevelOrthogonality`, `ActualFixedFunctionalBinaryMatrixMoment`, `ActualFiniteMomentLpBounds`, `ActualFixedFunctionalAppendOperator`, `ActualComplementCoordinateMassBridge`, and the Cmmsa/Tagged/Ordinary-star modules.
- **It still takes `hSpectral`.** Spectral47 is unproved.
- **Conclusion:** the hHC question is resolved as logical availability only. Material-moment, reduction, runtime and learning acceptance are not supported.

## 2. Exact-budget semantics: padding, whole fibre, eta, zero density, factor 2

- **The whole fibre is available at every budget.** `exactWholeRestriction n d r` has `r` zero rows, budget exactly `r`, and fibre `univ`. So `PseudorandomExact r eta b` is non-vacuous for every `r`, including `r` above any actual order. It forces mean ≤ `eta`, hence `eta ≥ 0`.
- **This refutes packet-7 F2 (HIGH).** The proposed vacuity counterexample does not apply. Negative-base `rpow` is unreachable because `eta < 0` makes the premise unsatisfiable. The case `eta = 0` forces `b ≡ false` and is handled explicitly. "Unrestricted eta" is literally true, but it has content only for `eta ≥ 0`.
- **Padding is checked.** `padOneLeftRow_fibre` is proved in both directions, and `padRestrictionToBudget` gives budget exactly `r` with the same fibre. So `pseudorandom_atMost_of_exact` holds: nominal-exact implies nominal at-most. The packet-8 complexity, non-claims and proof notes on raw versus actual budget are answered for the formal chain.
- **Actual exact-budget flag averaging is checked.**
  - `smaller_budget_zoom_density_le`: the divisor `gaussian (d-q)(a-q) > 0` follows from `had`.
  - Empty refined intervals contribute 0, via `hc0`.
  - `smaller_budget_of_exact_r` sets `a = r - (dim V - w)` and calls `hexact` at exactly budget `r`.
  - `exact_zoom_implies_nominal_pseudorandom` consumes `hR : R.budget = r`. That includes padded `R` with smaller actual order, which `actualOfRaw_order_le_budget` and `join_zeroKernel_codim_le_rows` route into `hbudget ≤ r`.
- **The strict guard is needed.** `r < d` gives `b < k` through `raw_left_rows_lt_free`, and that feeds `binary_target_half`, which is strict. The case `r = d` is not covered, and every consumer supplies a strict `r < 2h` or `r < c+s`.
- **Factor 2 and zero density.** The factor 2 comes from `fixed_residual_mean_le_two`. Dependent fixed columns give density 0 (`density_zero_of_fixed_dependent`).
- **The bound is one-sided.** `PseudorandomExact` is by definition an upper bound on density over nonempty fibres. Nothing here is a two-sided pseudorandomness theorem.

## 3. A22 scope, dependency direction and constants

- **`manuscript_A22_actual` is stated for natural, dyadic p.** It quantifies `{n d j p : Nat}` with `2 ≤ p`, `p = 2^k`, and `q = pConjugate p = p/(p-1)` as an exact real.
  - `realQNorm_holder_nat_pow` with `pConjugate_holder` supplies the conjugate pairing.
  - `HC46ExactContract` itself needs only dyadic `p ≥ 4`.
  - Packet-2 proof F4 (arbitrary real-p interpolation) is therefore not an obligation. I confirm Root's scope correction from these bodies.
- **The induction is not circular.**
  - Strong induction on `level` holds over all `n' d' eta g`.
  - Positive-cost parents use only `ih (level-1)`, through `a22_positive_parent_from_lowerIH`. Coverage is complete: `A ≠ ⊥` goes through the line `span{x}`, and `A = ⊥` with positive cost forces a hyperplane containing `B`.
  - The A14 witness coefficient `2^(3j)` gives `+6j` after squaring.
  - The zero-cost parent equals E exactly (`a22_zero_cost_energy`).
  - `a22_dual_energy_of_influences` runs only after influence ≤ E has been proved (`hclose E le_rfl …`).
  - Constants: `810j²m² ≤ 420j²p·m`, `420 ≤ 500`, and `500(j-1)²p + 6j ≤ 500j²p` (`a22_positive_exponent`). `a18BudgetScale j j = 2^(10j²)` is the same scale HC46 uses.
- **The order of use is consistent.** At a fixed level, A22 uses A18 and then A21. HC46 uses A22, then A18, then A21. The bodies of A18, A21 and the A14 witness lemmas are not in this window.
- **Legacy helper not credited.** `a22_parent_from_order_one_coordinate` is a requested native root, but it is conditional on `hderived`. Nothing on the A22 path in the inspected bodies calls it. Its docstring ("applied only after…") overstates its role.

## 4. Per-finding dispositions

| Finding (source) | Disposition | Evidence |
|---|---|---|
| P7 proof/complexity/non-claims F1 (HIGH): hHC still present | **Resolved** for the selected-leaf HC46 bound. **Bounded** for the material moment: hHC can be supplied, but there is no export, no native profile, no review coverage, and `hSpectral` remains. | `selected_leaf_HC46_original`, `selected_actual_material_moment_bound`, native stdout, pins |
| P7 F2 (HIGH) / NC F2: contract vacuity, `eta < 0` | **Resolved (refuted)** | `exactWholeRestriction*`, `boolean_mean_le_of_exact`, `original_HC46_exact` |
| P7 cx F4 / NC F5: exact versus lower-level budget | **Resolved** | `padRestrictionToBudget*`, `smaller_budget_of_exact_r` |
| P8 F1 / P8 cx F1 / NC F1: nominal premise stronger than actual exact-r | **Resolved** for the formal chain. **Retained** for manuscript wording. | `exact_zoom_implies_nominal_pseudorandom`, `ExactBudgetZoomBound` |
| P9 F1, F2, F3: budget exactly r, one-sided, ×2 | **Confirmed** as claim boundaries. The ×2 propagates as `eta = 2e`. | `failed_zoom_gives_nominal_pseudorandom`, application wrapper |
| P8 F6 / P9 F3: `r < d` | **Retained, necessary** (strict half-rank) | `raw_left_rows_lt_free`, `binary_target_half` (body outside this window) |
| P2 proof F4 / Q2: real-q | **Resolved** (natural dyadic p, real conjugate q) | `manuscript_A22_actual`, `pConjugate`, `realQNorm_holder_nat_pow` |
| P2 NC F1: influence includes order 0 | **Resolved internally.** The order-0 term is the energy bound in A22's conclusion, which is a stronger claim, and it is supplied before it is used. Manuscript fidelity is **retained**. | `a22_zero_cost_energy`, `hclose` |
| P1 F1: `a22_parent_from_order_one_coordinate` | **Retained Low.** Do not credit it. | ParentFactorization |
| P8 F1 NC: UNCOMPILED banners | **Resolved as identity:** the files are in the 319 closure and pinned, with no forbidden tokens. The banners carry no weight either way. | native evidence, banner membership |
| `hc46_rank_zero_exact` docstring ("remaining engine step"); AnalyticMoment header ("not proved locally") | **Low, stale.** HC46 is now proved elsewhere; Spectral47 is not. | ActualBinaryMatrixHC46, AnalyticMoment |
| `hEven` unused | **Info.** The theorem is stronger than the contract. | `original_HC46_exact` |
| P7 cx/NC F4: numerical usefulness of the HC46, failed-zoom and material constants | **Open** (numeric-NO gate) | `2^(500i²p)`, `(2e)^((p-2)/p)`, `selected_actual_analytic_rhs` |

## 5. Questions left for windows 2/3 (not resolvable from this window)

1. **A11:** the genuine strict-lower-degree discharge of `hS`. The cited span `a11_original_weighted_mixed_bound` / `manuscript_A7_actual` (lines 1207–1260) is unverified here.
2. **A9 and A8:** the actual A9 fibre and partition, `a9AmbientA8PartitionEquiv`, the coarse charge and the `a+b+k ≤ D` case split. The A8 overlap and cubic costs, and how `_horder` is discharged.
3. **DR6:** the signed incidence and 162 normalization. **A16, A18, A20, A21:** the bodies and their constants.
4. **Typed A14/A15 lemmas:** the definitions and transports `typed_A14_fixedLine/Hyperplane`, `a22_typed_*_witness_global` and `a22_A14_coefficient_le`.
5. **Boolean and raw bridges:** `exactPR_to_actual_normSqGlobal`, `complexRankProjection_boolean_eq`, `actualOfRaw_*`, `raw_left_rows_lt_free`, the elaborated type of `binary_target_half`, and `homogeneous_lift_density_le`.
6. **Coverage:** whether the material-moment support modules listed in §1 are intentionally outside the 170, and which artifact would review them.
7. **Manuscript fidelity:** whether HC4.6 is nominal or actual exact-r, whether influence includes order 0, and the constants 500/420/2e.
8. **Legacy A7/A9 absence:** this is bounded to the exact172 trace and the four focused consumers only. It is not an all-repository claim.

## 6. Exact safe claim boundary

Under explicit trust in the pinned Init/Mathlib/Batteries sources and the kernel, and given the qualified receipts, the following holds:
- The receipts show all seven native stages exiting 0, all 319 source pins and 566 warm objects unchanged, and 172 standard profiles. That is zero OWNED warnings and zero inherited regressions, not zero TOTAL warnings; inherited warning debt remains open.
- `original_HC46_exact` proves the unchanged `HC46ExactContract` with no added premise. Its content is only for `eta ≥ 0`, because negative `eta` makes the premise unsatisfiable.
- `manuscript_A22_actual` holds for natural dyadic `p ≥ 2` with real conjugate `q`.
- `selected_leaf_HC46_original` holds for the same `T` and `f`.
- `selected_leaf_failed_zoom_HC46_original` holds conditionally on `hfail`, `r < 2h` and `e ≥ 0`, with the one-sided parameter `2e`.

None of this establishes any of the following:
- the material moment or any hHC-free material export;
- Spectral47, or any useful numerical bound (numeric-NO);
- the source/star/robust8S, encoded reduction, runtime or learning gates;
- the upstream bridges, a fresh checkout or the final provider gates;
- manuscript, render or novelty fidelity;
- a new review of library bodies;
- review acceptance from native GREEN alone;
- any full-manuscript verdict.

Integration stays **INCOMPLETE** until windows 2 and 3 resolve §5.
