# Full89 integration, window 1 of 3 (contracts and selected consumer): independent complexity review

**Verdict for this window: GO-WITH-NOTES.** It covers only window 1 of 3.

- The integration as a whole stays **INCOMPLETE**. Windows 2 and 3 still have to cover A11, A9, A8, DR6 and the typed A14/A15/A16 bodies.
- This is not a milestone, material-moment, runtime, learning or manuscript verdict.
- No HIGH question that this window's source can address is left open. Both prior HIGH findings from packet 7 are resolved below from source. One residual item is kept as a Medium claim boundary.

I used no tools, wrote nothing and ran nothing. Native facts come from the receipts you supplied. Source hashes are compared only as text, window header against the all170 pin; I did not recompute any of them. Line numbers are not used; references are to declaration names.

## 1. Bodies supplied in this window: 13 inspected, 0 skipped

| File | Header hash vs all170 pin |
|---|---|
| ActualBinaryMatrixHC46A22ParentFactorization | A30B…DF7A, matches |
| ActualBinaryMatrixHC46A22OriginalInduction | B044…9BCA, matches |
| ActualBinaryMatrixHC46OriginalExactInhabitant | 6F56…6C95, matches |
| ActualSelectedComplementHC46OriginalApplication | 104A…B5B0, matches |
| ActualSelectedComplementAnalyticMoment | BFAE…92F9, matches |
| BinaryMatrixFourier | 8103…70D8, matches |
| ActualBinaryMatrixHC46 | 1C47…662C, matches |
| ActualBinaryMatrixHC46RealQNorm | FEB1…8C01, matches |
| ActualBinaryMatrixHC46RealQTransport | 3093…1B14, matches |
| ActualLeafLabelRankImageAlignment | 5991…80C2, matches |
| ActualFixedFunctionalMatrixLift | 1002…147F, matches |
| MatrixLiftNominalDirectComparison | E8C4…2E07, matches |
| MatrixLiftExactBudgetZoom | 4193…DD32, matches |

Packet 9's complexity report wrote the DirectComparison hash as "E8C4…E032". That is a transcription error. The exact pin is …2E07, and the reviewer's shorthand carries no weight for source identity.

**Native stdout.** I counted 172 root entries by module:

| Module group | Roots |
|---|---|
| A8 | 26 |
| A11 | 23 |
| A12 | 18 |
| A16 | 1 |
| A20 | 4 |
| A18 | 3 |
| A21 | 9 |
| A17 | 1 |
| RealQNorm | 14 |
| RealQTransport | 32 |
| OperatorLq | 10 |
| ParentFactorization | 13 |
| OriginalInduction | 10 |
| Inhabitant | 6 |
| Application | 2 |
| **Total** | **172** |

- Every profile is a subset of {propext, Classical.choice, Quot.sound}. `a21_exponent_le` uses {propext} only and `a21_density_recurrence` uses {propext, Quot.sound}. Neither contains `sorryAx` or a nonstandard axiom.
- `HC46ExactContract`, `Spectral47ExactContract` and `selected_actual_material_moment_bound` are **not** requested roots.

## 2. Main transitions, checked independently

### (a) `original_HC46_exact : HC46ExactContract`
It is a universal theorem with no hHC premise.

1. **Rank 0 (i = 0)** goes to `hc46_rank_zero_exact`, which has two branches:
   - η ≤ 1: `binary_hc_rankZero_exact`.
   - η > 1: the normalized ‖·‖ is the mean, the mean is ≤ 1, and 1 ≤ η^α.
2. **Rank i ≥ 1:**
   - η ≥ 0 is *derived*, from `uniformMean_indicator_nonneg` together with `boolean_mean_le_of_exact`. The bound δ = min(η, 1) is internal.
   - **δ = 0 branch:** zero energy forces b ≡ false (`original_HC46_boolean_zero_of_energy_zero`), so the norm is 0, which is ≤ RHS.
   - **δ > 0 branch:** the chain is `exactPR_to_actual_LqGlobal` (parameter is literally `(min eta 1)^(1-1/p)`, which settles packet 1's open question 1) → `manuscript_A22_actual` → `actual_A18_original_global` → `manuscript_A21_actual`.
3. **Exponent algebra, rechecked by hand:**
   - Coefficient: 200i²p² + (10i² + 500i²p)(p/2 − 1) ≤ 450i²p² + 5i²p ≤ 455i²p² ≤ 500i²p².
   - Density exponent: 1 + (1 − 1/p)(p − 2) = p − 2 + 2/p ≥ p − 2. Since δ ≤ 1, `rpow_le_rpow_of_exponent_ge` applies in the correct direction.
   - Taking the p-th root, then using δ ≤ η with exponent (p − 2)/p ≥ 0, gives exactly the contract RHS `2^(500 i² p)·η^((p−2)/p)`.

### (b) The HC46 contract is not vacuous (resolves packet 7 F2 / packet 7 complexity F3)
`PseudorandomExact r δ f` has the form ∀R, budget = r → fibre nonempty → density ≤ δ, where the budget is *nominal*.

- `exactWholeRestriction n d r` has `rows := r`, all-zero matrices, budget r and fibre `univ`, which is always nonempty.
- So for **every** r, the premise implies mean ≤ η, and therefore η ≥ 0.
- The packet 7 refutation needs the premise to hold vacuously once r exceeds the maximum actual order. That cannot happen with a nominal budget.
- Its two concrete cases also fail:
  - η = 0 with b ≡ true: the premise is false, since the mean is 1.
  - η < 0: the premise is unsatisfiable.
- **Disposition: resolved from source.** `BinaryMatrixFourier.exactWholeRestriction_fibre` and `boolean_mean_le_of_exact` are the evidence.

### (c) Original A22 with natural dyadic p and real conjugate q
`manuscript_A22_actual` is stated over `{n d j p : Nat}`, with `2 ≤ p`, `∃k, p = 2^k`, and globalness at `pConjugate p = p/(p−1)` (real, not rounded).

- Duality uses the exact pairing identity `a22_projection_pairing` together with `realQNorm_holder_nat_pow`. That gives E^p ≤ moment·‖f‖_q^p ≤ moment·ε^p.
- The moment comes from A21 at **natural dyadic p** only. No interpolation to non-dyadic exponents is needed or claimed. This closes packet 2's F4 as "not required by this statement".
- Whether the manuscript states A22 more generally is a manuscript-fidelity question and stays open.
- **Induction:** strong induction on the level, generalized over all n′, d′, η and g.
  - Positive-cost parents use only `ih (level−1)`, with 1 ≤ level derived from the parent's positivity.
  - The zero-cost parent equals E (`a22_zero_cost_energy`).
  - The dual estimate is called only after `OriginalActualInfluenceThrough level E` has been **proved**: either E ≤ B closes the case directly, or B < E and `hclose E le_rfl`.
  - Level 0 is handled separately.
- **Constants:**
  - 200j²(2m)² + 10j²(m − 1) ≤ 810j²m² ≤ 840j²m² = 420j²p·m.
  - 500(j − 1)²p + 6j ≤ 500j²p, because (j − 1)² + j ≤ j² and 6j ≤ 500jp.
- **Dependency direction:** Lq globalness → A22 (influence) → A18 (norm-squared globalness at 2^(10j²)·E) → A21 (moment). Neither A18 nor A21 imports A22, so there is no cycle.

### (d) ParentFactorization
- Coverage is exhaustive. A ≠ ⊥ gives a domain line `span{x}` with outer codomain ⊤. A = ⊥ forces B ≠ ⊤, and `exists_hyperplane_containing_of_ne_top` then gives a containing hyperplane.
- Cost is exact: `relative_endpoint_cost_add` gives cost = 1 + inner, so inner ≤ j − 1.
- Witness globalness uses `a22_A14_coefficient_le` (≤ 2^(3j)). Squaring adds +6j.
- All transports are equalities: A1 composition, `a22_intrinsic_energy_reindex`, and Fintype subsingleton bridges. Normalization is never lost.
- `a22_parent_from_order_one_coordinate` is **not** on the A22 path. See N2.

### (e) Selected leaf consumer
- `selected_leaf_HC46_original` passes `original_HC46_exact` into `selected_leaf_HC46_of_exact_PR`, applied to the same `T` and `f`, with `hEven := rfl` (d = 2h).
- The failed-zoom variant composes it with `selected_leaf_failed_zoom_PR`, which gives η = 2e, using the same `T` throughout.
- `leafMatchBit_eq_matchingLeafSet` identifies the actual leaf predicate with the manuscript predicate on the same predrawn table and functional.
- `hfail` ranges over every decoded pair. That includes `pairOfGlobal Q W f`, so the f-specific agreement is covered.

### (f) Exact-budget, nominal-budget and factor-2 bridge (`exact_zoom_implies_nominal_pseudorandom`)
- **Padding:** `padOneLeftRow_fibre` is proved in both directions and `padRestrictionToBudget` preserves the fibre. Together they give `pseudorandom_atMost_of_exact`: the exact nominal-budget-r premise is equivalent to the at-most-r premise.
- **Dependent fixed columns:** `density_zero_of_fixed_dependent` gives density 0, which is ≤ 2e because e ≥ 0.
- **Strict rank guards:** the order is ≤ the budget, which is r, and r < d = a + k. Hence b < k (`raw_left_rows_lt_free`), and `targetRank_lt` feeds `binary_target_half`.
- **Budget bound:** `join_zeroKernel_codim_le_rows` gives a + codim W ≤ a + b ≤ r.
- **Flag averaging** (`smaller_budget_of_exact_r` / `smaller_budget_zoom_density_le`):
  - Set a = r − codim. Then q ≤ a ≤ d, using r < d.
  - The flag identity `sum_refine_flags_constant` has divisor gaussian(d − q, a − q) > 0.
  - Empty refined intervals contribute exactly 0.
- **Factor 2:** `fixed_residual_score_cross` relies on full-rank targets having equal scores and on targetCard < 2·#surjective. Every denominator is proved positive (`hfibre` comes from `freeCard = targetCard·fibreCard > 0`).
- The result is **one-sided**: it gives density ≤ 2e and nothing more.

## 3. Dispositions of earlier findings, as far as this window's source reaches

| Source of finding | Severity | Disposition |
|---|---|---|
| P7 proof F1 / P7 complexity F1 (consumer still takes hHC) | HIGH | **Resolved for the milestone consumer.** `selected_leaf_HC46_original` takes no hHC premise, and the contract is discharged by a universal theorem. The material question is separated out as N1 (Medium). |
| P7 proof F2 / P7 non-claims F2 (vacuity, negative η) | HIGH / Med | **Resolved.** See §2(b). |
| P8 F5 / P8 complexity F1 / P8 non-claims F1 (nominal exact budget is stronger than an actual exact-r premise) | Med | **Resolved inside the route; manuscript fidelity still open.** Within the consumer, PR is *derived* from the actual exact-r zoom premise (`hfail` → `ExactBudgetZoomBound`) through the flag bridge. It is never assumed from a manuscript-level actual exact-r claim. Only `selected_leaf_HC46_original` takes `hPR` raw, and it states that hypothesis explicitly. |
| P9 F1/F2, P7 complexity F4 (budget exactly r; one-sided) | Med | **Resolved, with a recorded boundary.** Padding makes exact-r and at-most-r equivalent. The bound is an upper density bound only, and the HC46 proof uses only upper bounds (`boolean_mean_le_of_exact`, `exactPR_to_actual_normSqGlobal`). It is never a two-sided pseudorandomness theorem. |
| P8 F6 (`r < d` stricter than necessary) | Low | **Kept as a boundary.** r = d is not covered. Consumers supply `hrd : r < 2h` or `r < c+s`. |
| P2 F4, packet 2 scope correction (real p versus real q) | Integration | **Confirmed** from the A22, RealQNorm and RealQTransport bodies. See §2(c). |
| P1 Q1 (`exactPR_to_actual_LqGlobal` parameter) | Integration | **Confirmed.** It is `(min η 1)^(1−1/p)`, definitionally equal to the `hLqi` ascription. |
| P2 non-claims (influence includes order 0) | Low | **Internally consistent.** A22 proves the order-0 bound (`a22_zero_cost_energy`), so the stronger A18 premise is supplied rather than assumed. Manuscript fidelity is open. |
| P8 F1 (five draft "UNCOMPILED" banners) | Med | **Provenance closed.** The five files are pinned in the 319-file closure and have native exit 0. The banners have no evidential weight in either direction. Compiled does not mean certified. |
| P8 F4 (bridge `def`s with inferred types) | Low | **Bounded.** The three `binary_affine_target_*` aliases are absent from the trace. The route uses `binary_target_half`, whose use is pinned by the kernel (`exact_mod_cast` to targetCard < 2·#surjective). |
| P1 F1 / P1 complexity F1 (`a22_parent_from_order_one_coordinate`) | Low | **Confirmed.** See N2. |

## 4. New notes from this window

- **N1, Medium (claim boundary).** `selected_actual_material_moment_bound` still takes `hHC` and `hSpectral`.
  - **Logically available:** `original_HC46_exact` has exactly the type `ActualSelectedComplementAnalyticMoment.HC46ExactContract`. It is the same constant, because OriginalExactInhabitant imports AnalyticMoment. So it can fill `hHC` in that same consumer, for the same `Tc`, `fc`, `r` and η = 2e.
  - **No dedicated export exists:** no supplied declaration performs that instantiation, and none is natively checked or a root. Such a declaration would have to live in a module that imports the Inhabitant; AnalyticMoment cannot import it without a cycle.
  - Even after instantiation, the result remains conditional on `Spectral47ExactContract`, `hfail` and `hsel`.
  - Numerical usefulness is not established. The low-level prefactor is about 2^(4000r²m²) against η^(≈m − 1/2), and the high energies are unbounded.
  - Do not claim an hHC-free material-moment, reduction, runtime or learning result.
- **N2, Low.** `a22_parent_from_order_one_coordinate` is a requested root but is conditional on `hderived`. Neither `a22_positive_parent_from_lowerIH` nor `manuscript_A22_actual` calls it. Its docstring ("applied only after…") overstates its use, so it must not be credited as an unconditional fact.
- **N3, Low (stale documentation, no evidential weight):**
  - `hc46_rank_zero_exact` says the positive-rank step is "remaining".
  - `selected_actual_event_moment_bound` says hdecomp is the "sole remaining obligation".
  - `carrierFibreQNorm_hyperplane_coordinate` says "line".
- **N4, Info.**
  - `hEven` is unused in the i ≥ 1 branch.
  - `hR` is consumed as `rw [hR]`, so ≤ would have sufficed.
  - `hklt` is unused in `selected_actual_HC_spectral_moment_bound`.
  - None of these affects soundness.

## 5. Questions left for windows 2 and 3, and for external gates

1. **A11:** that `a11_original_weighted_mixed_bound` genuinely discharges `hS`, and that `manuscript_A7_actual` uses strict lower-degree simultaneous induction. The trace only shows that A11 is reached and the legacy A7 helpers are not; that does not establish the mathematics.
2. **A9 and A8:** the A9 fibre and partition (`a9AmbientA8PartitionEquiv`, coarse charge, the a + b + k ≤ D versus > D split, the `_horder` discharge), the A8 overlap, the cubic m³ cost, and the 6Dk budget.
3. **DR6:** signed incidence, the normalization 162, the 2^(6D²) and 2^(7D(i+j)) constants, and the `DR6F2Obstruction` definition.
4. **Typed lemmas consumed here only through their types:**
   - `typed_A14_fixedLine` / `typed_A14_fixedHyperplane`
   - `a22_typed_*_witness_global`
   - `typed_*_A1_operator_step`
   - `filteredCarrierFunction_energy_le_A16`
   - the definition of `a18BudgetScale`
   - `exactPR_to_actual_normSqGlobal`
   - `complexRankProjection_boolean_eq`
   
   The kernel confirms each use matches the stated type. Whether those types are faithful to the manuscript is not shown.
5. **Manuscript fidelity:** the PseudorandomExact premise (nominal budget, one-sided), the HC4.6 and A22 statements and constants (500, 420, the (p−2)/p exponent), and the influence definition.
6. **Spectral47, numeric NO, source/star/robust8S, encoded reduction, runtime/learning, upstream, fresh checkout, final provider, manuscript/render/novelty:** all open.
7. **Warnings and library trust:**
   - Zero owned warnings and zero inherited regressions are established. That is not zero total warnings; the inherited baseline debt remains open.
   - Init, Mathlib and Batteries are trusted at their pinned versions and were not newly reviewed.

## 6. Safe claim boundary for this window

The following is established by these sources together with the qualified native receipts:

- The universal theorem `original_HC46_exact : HC46ExactContract` holds for unrestricted real η, including η = 0 and η > 1, and its premise is non-vacuous for every r.
- The original `manuscript_A22_actual` holds for natural dyadic p ≥ 2 with real conjugate q = p/(p − 1), across all finite binary spaces, by strict lower-level induction, with the influence premise of the duality step proved rather than assumed.
- `selected_leaf_HC46_original` and `selected_leaf_failed_zoom_HC46_original` apply it, with no hHC premise, to the same predrawn leaf `T` and functional `f`. Through padding and exact-budget flag averaging, the failed-zoom premise yields the one-sided upper density bound `PseudorandomExact r (2e)` under r < d and e ≥ 0.

The following is **not** established:

- an hHC-free material-moment declaration, or any Spectral47-free one;
- useful numerical bounds;
- two-sided pseudorandomness;
- the A11, A9, A8 and DR6 mathematics, which belong to windows 2 and 3;
- manuscript fidelity;
- acceptance of the milestone or the full manuscript.
