# Full89 integration, window 1 of 3 (contracts and selected consumer): proof-adversarial review

## Verdict for this window: GO-WITH-NOTES

This verdict covers window 1 only. The integration as a whole stays **INCOMPLETE** until windows 2 and 3 review the A7–A21 bodies, and no full-manuscript verdict is given.

- **Bodies:** all 13 complete bodies supplied in this window were read in full. None was skipped.
- **The two HIGH findings from packet 7 are resolved from this window's source.** The vacuity question is fully closed. The hHC question is closed for the selected-leaf consumer. For the material consumer, removing hHC is logically available, but no dedicated declaration exists yet; that is kept as a Medium note.
- **Window 1 adds no new HIGH finding.**
- **Method:** I used no tools and ran no code. Each file header's SHA matches its all170 pin, but I could not hash the text itself. I cite declarations by name; I did not verify Root's line numbers.

## 1. Coverage

| # | File | Pin | Status |
|---|---|---|---|
| 1 | ActualBinaryMatrixHC46A22ParentFactorization | A30B756D… | inspected |
| 2 | ActualBinaryMatrixHC46A22OriginalInduction | B044690D… | inspected |
| 3 | ActualBinaryMatrixHC46OriginalExactInhabitant | 6F56EAF2… | inspected |
| 4 | ActualSelectedComplementHC46OriginalApplication | 104A7BF7… | inspected |
| 5 | ActualSelectedComplementAnalyticMoment | BFAE5D2E… | inspected |
| 6 | BinaryMatrixFourier | 810324DD… | inspected |
| 7 | ActualBinaryMatrixHC46 | 1C47B86B… | inspected |
| 8 | ActualBinaryMatrixHC46RealQNorm | FEB199D9… | inspected |
| 9 | ActualBinaryMatrixHC46RealQTransport | 30933F34… | inspected |
| 10 | ActualLeafLabelRankImageAlignment | 5991FC3D… | inspected |
| 11 | ActualFixedFunctionalMatrixLift | 1002E7F8… | inspected |
| 12 | MatrixLiftNominalDirectComparison | E8C4A795… | inspected |
| 13 | MatrixLiftExactBudgetZoom | 4193FABC… | inspected |

**Lemmas this window calls but whose bodies sit in other packets.** I reused their prior three-lens reports, assuming their source identities are unchanged; I did not re-review them here:
- A18, A21 and A12 statements: `actual_A18_original_global`, `manuscript_A21_actual`, `a12Energy`, `OriginalActualInfluenceThrough`.
- Typed A14/A1/A22 witness lemmas: `typed_A14_fixedLine` and `typed_A14_fixedHyperplane`, `typed_line_A1_operator_step` and `typed_hyperplane_A1_operator_step`, `a22_typed_*_witness_global`, `a22_A14_coefficient_le`, `manuscript_A1_complex`.
- Boolean and pseudorandom bridges: `exactPR_to_actual_normSqGlobal`, `complexRankProjection_boolean_eq`.
- Raw/actual restriction conversions: `actualOfRaw*`, `rawOfActual*`.
- Matrix-lift lemmas: `raw_left_rows_lt_free`, `binary_target_half`, `homogeneous_lift_density_le`.

## 2. Per-finding dispositions

### R1 — was HIGH (packet 7, all three lenses): "selected consumer retains hHC"

**Selected-leaf consumer: RESOLVED.**
- `HC46ExactContract` is a closed, parameter-free `Prop`, defined in AnalyticMoment.
- `original_HC46_exact : HC46ExactContract` is a native root with a standard axiom profile. Its module imports AnalyticMoment, so there is no cycle.
- `selected_leaf_HC46_original` is the term `selected_leaf_HC46_of_exact_PR T f hPR hi hp4 hpDyadic original_HC46_exact`. It keeps the same `T`, the same `f`, `d = 2h` (`hEven := rfl`), and no hHC argument.
- `selected_leaf_failed_zoom_HC46_original` builds `hPR` for that same `rankImageBoolean (leafMatchBit T f)`. The path is `selected_leaf_failed_zoom_PR` → `actual_leaf_failed_zoom_gives_nominal_pseudorandom` → `failed_zoom_gives_nominal_pseudorandom`, then a rewrite by `actualLeafRankImage_eq_matchingLeafSet`. The parameter is exactly `2e`, and the theorem keeps `r < 2h`, `0 ≤ e` and `hfail` as premises.

**Material-moment consumer: logical availability established; no dedicated export (Medium, retained).**
- `selected_actual_material_moment_bound` uses `hHC` only through `selected_actual_HC_spectral_moment_bound` → `selected_low_append_HC46_lpNorm_bound`, applied as `hHC hEven b hPR hiR hp4 hpDyadic`. Here `b = selectedF Tc fc`, `d = c+s`, and `hEven = hsplit`.
- The contract is universal over n, d, h, r, i, p and eta, so `original_HC46_exact` fits that argument exactly.
- However, no supplied declaration and no native root performs this composition. The material theorem is not among the 172 roots.
- Its imports include modules that are absent from the all170 pins: ActualSelectedSpectralParameters, ActualFiniteMomentLpBounds, ActualAppendFourierCrossLevelOrthogonality, ActualRankImageRightBasisInvariance, ActualFixedFunctionalBinaryMatrixMoment, ActualFixedFunctionalAppendOperator, MatrixGrassmannIdentity, and the Cmmsa/Tagged/Ordinary-star families. ActualSelectedComplementAppendMoment is pinned but flagged `transitively_consumed: false`.
- So the material bound falls outside both the root trace and the reviewed-body set. Even if hHC were removed, it would still depend on `hSpectral` (Spectral47 is open), `hsel`, `hfail` and the unreviewed bodies above.
- **Required evidence:** a dedicated declaration, e.g. `selected_actual_material_moment_bound_original` with `hHC := original_HC46_exact`, together with its native axiom profile and a review of the uncovered bodies.

### R2 — was HIGH (proof packet 7 F2; complexity packet 7 F3; non-claims packet 7 F2): "HC46ExactContract may be vacuous or refutable"

**RESOLVED.**
- `PseudorandomExact r δ f` quantifies over every nominal-budget-r restriction with a nonempty fibre.
- `exactWholeRestriction n d r` (zero columns, r zero rows, zero values) has budget exactly r and the whole space as its fibre, for every r, n and d. So the premise is never vacuous.
- `boolean_mean_le_of_exact` then gives `0 ≤ mean ≤ δ`, which forces `eta ≥ 0`. The proposed counterexamples (eta = 0 with b ≡ true; eta < 0 with `Real.rpow`) have unsatisfiable premises.
- Independently, the contract is inhabited by a standard-axiom proof. It therefore cannot be refutable unless the pinned kernel and libraries are themselves inconsistent.

### R3 — `original_HC46_exact` body (unrestricted eta and zero density): verified

- **i = 0:** handled by `hc46_rank_zero_exact`. The eta ≤ 1 branch uses `binary_hc_rankZero_exact`. The eta > 1 branch uses `‖proj₀‖ ≤ 1 ≤ eta^α`. `_hEven` is unused, which makes the result strictly stronger.
- **i ≥ 1:** `delta = min eta 1`.
  - **delta = 0:** this forces `f = 0` (`original_HC46_boolean_zero_of_energy_zero`), hence `indicator b = 0` and `lpNorm = 0`. The right-hand side is nonnegative because eta ≥ 0.
  - **delta > 0:** the chain is `exactPR_to_actual_LqGlobal` (order ≤ r, parameter `delta^(1-1/p)` by definition of the `let`), restricted to order ≤ i via `hQ.trans hi`, then `manuscript_A22_actual`, then A18 at D = r = i (`a18BudgetScale i i = 2^(10i²)·`), then A21. `hprojection` gives E ≤ delta.
- **Arithmetic, checked by hand:**
  - The coefficient is ≤ 455·i²p² ≤ 500·i²p².
  - The density exponent is `1 + (1-1/p)(p-2) = p-2+2/p ≥ p-2`, and the exponent is applied in the correct direction because delta ≤ 1.
  - Taking the p-th root gives `2^(500i²p)·delta^((p-2)/p)`, and `delta ≤ eta` is used with a nonnegative exponent.
- **Result:** no hHC premise, no eta ≤ 1 premise and no basis-invariance premise. This also resolves packet 1 Q1: the parameter shape `(min eta 1)^(1-1/p)` is confirmed.

### R4 — packet 2 F4/Q2: "real-q A22 needs interpolation"

**RESOLVED.** Root's scope correction is confirmed against source.
- `manuscript_A22_actual` takes `{n d j p : Nat}`, `2 ≤ p`, `∃k, p = 2^k`, and globalness `UpToActualLqGlobal j (pConjugate p) eps f`.
- `pConjugate p = p/(p-1)` is real. At p = 4 it equals 4/3, so q really is non-integer.
- The dual step uses `realQNorm_holder_nat_pow` (natural power p, true real-q norm). The pairing equals exactly E (`a22_projection_pairing`). This gives `E^p ≤ moment·eps^p`, and A21 is applied only at dyadic p.
- No real p and no interpolation is required by this theorem. The HC46 contract also needs only dyadic p ≥ 4.
- Whether the manuscript states A22 in this natural-dyadic-p form is a manuscript gate and remains open.

### R5 — A22 induction structure: verified

- **Induction:** strong induction on `level`. The motive quantifies over all n', d', eta and g, and `ih (level-1)` is used only when cost > 0 (which gives level ≥ 1).
- **Order-one parents are covered exhaustively:**
  - If A ≠ ⊥: the line `span{x}` with outer endpoint ⊤.
  - If A = ⊥ and B ≠ ⊤: a codimension-one H ⊇ B.
  - Both use the exact additive cost `relative_endpoint_cost_add`. The witness scale `2^(3j)` squares to `+6j`.
- **The dual estimate is never given an assumed premise.** Zero cost equals E exactly (`a22_zero_cost_energy`). In the branch E > B, `hclose E le_rfl` proves `OriginalActualInfluenceThrough level E` before `a22_dual_energy_of_influences` uses it. Level 0 is handled separately.
- **Exponents:**
  - With p = 2m: 200j²·4m² + 10j²(m−1) ≤ 810j²m² ≤ 420j²p·m.
  - 500(j−1)²p + 6j ≤ 500j²p.
  - 420 ≤ 500.
- **Order-0 inclusion (non-claims packet 2 Q):** `OriginalActualInfluenceThrough` includes cost-0 carriers. A22 proves that case exactly rather than assuming it, so it is internally sound. Manuscript fidelity of the definition remains open (Low).

### R6 — packet 8 F1/F5 (all three lenses): "nominal padding makes PseudorandomExact stronger than the manuscript's actual exact-r condition"

**RESOLVED for this route; manuscript wording remains open.**
- `pseudorandom_atMost_of_exact` (zero-row padding: `padRestrictionToBudget`, with fibre and density unchanged) shows that nominal-exact-r is equivalent to nominal-at-most-r.
- In the selected chain, `PseudorandomExact` is never assumed from a manuscript condition. It is *derived* from `ExactBudgetZoomBound`, which is actual exact-r on nonempty Grassmann zooms, by `exact_zoom_implies_nominal_pseudorandom`.
- I checked that derivation:
  - `hR : R.budget = r` is used only as `≤ r`.
  - Actual order ≤ budget comes from `actualOfRaw_order_le_budget`.
  - `join_zeroKernel_codim_le_rows` gives `a + codim W ≤ r`.
  - Smaller actual budgets are reached by flag averaging (`smaller_budget_of_exact_r` / `homogeneous_lift_density_of_exact_r`): `a' = r − codim`, with `q ≤ a' ≤ q+k` following from `hbudget` and `r < q+k`.
  - The Gaussian divisor `gaussian(d−q)(a−q) > 0`, and empty refined zooms contribute 0.
- **Strict guards:** `hbk : rank < k` is derived from `r < d`, and `binary_target_half` is applied under `targetRank < k`.
- **Dependent fixed columns:** this case gives density 0 (`density_zero_of_fixed_dependent`).
- **Upper-to-zoom reduction:** in `failed_zoom_gives_exact_bound`, Q ⊄ W contradicts a nonempty interval, and `Zoom ≃ Between` holds by `Equiv.refl`.

### R7 — packet 9 F1/F2 (and the non-claims lens): "budget exactly r, one-sided bound, factor 2"

**Confirmed and consistent.**
- `PseudorandomExact` is a one-sided upper bound on density. It is not a two-sided theorem, and it should not be described as one.
- HC46 consumes only the upper bound (density, then energy, then Lq).
- The factor ×2 is carried exactly as `2e`.
- `r < d` is an explicit premise (`r < 2h` or `r < c+s`). The regime r ≥ d is not covered (Low).
- Complexity packet 7 F4 (`hfail` exact-r versus all levels i ≤ r) is resolved: lower orders are covered by the padding and flag-averaging route above.

### R8 — packet 8 F1: five "UNCOMPILED" banners

**RESOLVED as stale.**
- GrassmannCounting, GrassmannFlagPosterior and the MatrixGrassmann* files are imported by MatrixLiftExactBudgetZoom and are pinned in the verified 319-file closure.
- The banners carry no evidential weight in either direction. Native GREEN status is still not review acceptance.

### Low and Info notes (retained)

- **L1 (packet 1 F1).** `a22_parent_from_order_one_coordinate` is a native root, but it is conditional on `hderived` and is not used on the main A22 path. Its docstring ("applied only after…") overclaims. It may be credited only as a conditional lemma.
- **L2.** Stale docstrings, given no weight: `hc46_rank_zero_exact` ("positive-rank … remaining"), the AnalyticMoment header (its contracts are now partly inhabited elsewhere), and `selected_actual_event_moment_bound`'s description of `hdecomp`.
- **L3.** The roots include proper-subset axiom profiles (`a21_exponent_le` uses only `propext`; `a21_density_recurrence` uses `propext` and `Quot.sound`), which is harmless. Non-root dependencies of this window are covered transitively by the root profiles; examples are `exact_zoom_implies_nominal_pseudorandom`, `selected_leaf_HC46_of_exact_PR`, `hc46_rank_zero_exact` and `pseudorandom_atMost_of_exact`.

## 3. Native and trust boundary

- The receipts establish the following; I re-ran none of it:
  - all seven native stages exited 0;
  - all 172 root profiles are standard;
  - all 319 source pins verified; 566 cached objects unchanged;
  - trace and capture identities match;
  - 0 owned error headers, 0 owned warnings and 0 inherited regressions.
- Zero owned warnings is not zero total warnings. The inherited warning-baseline debt remains open.
- Trust in the pinned Init, Mathlib and Batteries sources and kernel is explicit. For example, I did not re-review `Real.inner_le_Lp_mul_Lq_of_nonneg`, `Real.Lp_add_le_of_nonneg` or `Real.HolderConjugate.conjExponent`.
- Legacy-absence claims (the A7 `a7_a9_*` helpers, the A9 `a9_initial_datum_card` and `a9_fiber_triple`, and the inferred-type bridge aliases) apply only to the exact 172-root trace and the four focused consumers. These legacy helpers get no credit.

## 4. Unresolved questions for windows 2 and 3

The bodies needed to answer these were not in window 1, so I retain them rather than endorsing Root's dispositions.

1. **A11:** does `a11_original_weighted_mixed_bound` genuinely supply `hS`, and does `manuscript_A7_actual` construct the strict lower-degree IH (Root's claim about lines 1207–1260)? Also the overlap and multiplicity payment, the A10 saving and the i/j tails.
2. **A9 and A8:**
   - the A9 actual partition (`a9AmbientA8PartitionEquiv`) and coarse charge;
   - the support-window case split `a+b+k ≤ D` versus `> D`;
   - discharge of `_horder`;
   - A8's cubic loss and its `6Dk` against `3Dk` budget.
3. **DR6:** the signed-incidence and Möbius normalisation; the `DR6ComplexOrdinaryFilter` versus `DR6OrdinarySelected` bridge; the constants 1/162, 2^(6D²) and 2^(7D(i+j)).
4. **A18 and A21 exact statements:** the definition of `a18BudgetScale` (only its value at (j, j), 2^(10j²), is pinned here by `ring`), `a18_lower_absorption`, the nine-over-512 absorption lemma, and the exact hypotheses of `manuscript_A21_actual`. The direction A18/A21 → A22 is confirmed by imports, since Lean forbids import cycles.
5. **Typed A14, A15 and A16:** the definitions and transports, `filteredCarrierFunction_energy_le_A16` (a cost-unconditional bound of 2^(11D²)), and the typed witness and A1 operator-step lemmas.
6. **Matrix-lift bodies in other packets:** `binary_target_half`, `raw_left_rows_lt_free`, and `fullRank_target_score_eq` without a surjectivity hypothesis on Y.
7. **The dedicated material export and review of the uncovered bodies (R1),** plus Spectral47 and the numerical usefulness of `selected_actual_analytic_rhs`.

## 5. Safe claim boundary

**May be claimed.** Assuming the pinned kernel and library trust, the qualified native receipts, and the prior reports on the lemmas listed in §1:
- The Lean declaration `original_HC46_exact : HC46ExactContract` is kernel-checked with standard axioms. It covers unrestricted real eta, including eta = 0 and eta > 1. It has no hHC, eta ≤ 1 or basis-invariance premise, and it derives eta ≥ 0 internally.
- `manuscript_A22_actual` is checked for natural dyadic p ≥ 2 with real conjugate q = p/(p−1), over all finite binary matrix spaces, with an unrestricted eps parameter.
- `selected_leaf_HC46_original` and `selected_leaf_failed_zoom_HC46_original` apply that contract to the same predrawn T and f with no hHC premise. The failed-zoom version gives the parameter 2e and keeps `r < 2h`, `0 ≤ e` and `hfail` as explicit premises.
- `PseudorandomExact` here is a nominal-budget, one-sided density upper bound. In the failed-zoom route it is derived from actual exact-r zoom bounds by flag averaging.

**Must not be claimed:**
- an hHC-free material-moment theorem as a checked declaration;
- any Spectral47, numerical NO, material-moment, reduction, runtime, learning, upstream, fresh-checkout or final-provider acceptance;
- a two-sided pseudorandomness theorem;
- that `hfail` is satisfiable with a useful e;
- the correctness of A7–A21 internals before windows 2 and 3;
- manuscript, render or novelty fidelity of the constants (500, 420, ×2) or of the definitions;
- zero total warnings;
- library bodies being newly reviewed;
- any full-manuscript verdict.
