# Full89 integration synthesis (non-claims lens): all three windows and all three lenses

## Verdicts

| Scope | Verdict |
|---|---|
| **Selected-leaf / native integration** (original natural-dyadic-p A22 with real conjugate q, unrestricted-η HC46, and the same pre-drawn T/f selected-leaf consumer) | **GO-WITH-NOTES** |
| **Full material-moment / manuscript readiness** | **INCOMPLETE.** No readiness claim is supported. |
| **Overall integration GO** | **Not issued.** The native verdict above is the strongest one available. |

- No HIGH issue stays unresolved within the native scope.
- The HIGH question that window 2 carried forward, and window 3 retained, splits in two:
  - For the selected-leaf consumer it is resolved directly from source.
  - For the material-moment consumer it becomes an open material obligation. It does not block the native verdict, but it does block any material verdict.

## Coverage

| Item | Count | How it was used |
|---|---|---|
| Cross-partition complete bodies supplied | 35 | 35 inspected, 0 skipped (window 1: 13, window 2: 10, window 3: 12) |
| Window reports | 9 | All read |
| Prior packet reports | 27 | All read |
| Remaining selected bodies | 135 of 170 | Not re-inspected. I relied on their prior three-lens reports, only under the pinned source hashes and native identities. |

- I used no tools, wrote no files and ran no Lean or Lake. The receipts are accepted only to the extent they state.
- I did not recompute any hash.
- Reviewer hash transcriptions carry no identity weight. For example, window 1 non-claims row 11 is garbled; the authoritative FixedFunctionalMatrixLift pin is 1002E7F8…147F.

## Evidence tiers

This replaces a reading that prior wording invited.

**Correction.** Compiling all 319 modules does **not** give every constant in them a standard axiom profile. The fresh `#print axioms` evidence covers exactly the 172 requested roots and their transitive constant closures. The `"standard_axiom_profiles": true` flag must be read with that scope. Compilation with zero owned warnings rules out owned `sorry` warnings, but it does not show that an unreached declaration is free of `axiom`, nor does it give such a declaration an axiom profile.

| Tier | Meaning | Examples |
|---|---|---|
| **T1: reached** | In the 172-root / focused-four closure: compiled, with a standard transitive profile | All 172 roots, including `a22_parent_from_order_one_coordinate`, and their reached dependencies (`selected_leaf_HC46_of_exact_PR`, `hc46_rank_zero_exact`, `exact_zoom_implies_nominal_pseudorandom`, `pseudorandom_atMost_of_exact`, `dr6_actual_complex_fourth_moment_over_162_le`, `a9AmbientA8PartitionEquiv`, and the reached A7Transfer constants listed in the receipt) |
| **T2: compiled, not reached** | Source and object pinned inside the 319; **no** axiom profile | `selected_actual_material_moment_bound` (its body calls `ActualSelectedComplementAppendMoment.selected_actual_append_moment`, and that module is pinned `transitively_consumed: false`); all of AppendMoment; ActualBinaryMatrixHC46TypedA14Energy and ActualTypedIntrinsicWitnessNaturality (imported by ParentFactorization, no constant consumed); A17FixedSlice; A17DerivativeGlobalTransfer; every `*Checks` module; the legacy `a7_a9_preceding_*` lemmas, `a7_a9_zero_parent_family_le`, `a9_initial_datum_card`, `a9_fiber_triple`; the three `binary_affine_target_*` alias `def`s |
| **T2′: compiled, not reached, not selected** | Bodies never reviewed in this campaign | Imports of AnalyticMoment outside the 170: ActualSelectedSpectralParameters, ActualFiniteMomentLpBounds, ActualAppendFourierCrossLevelOrthogonality, ActualRankImageRightBasisInvariance, ActualFixedFunctionalBinaryMatrixMoment, ActualFixedFunctionalAppendOperator, ActualComplementCoordinateMassBridge, MatrixGrassmannIdentity, and the Cmmsa / Tagged / OrdinaryStar families. Also A9ActualFiber, CommonDerivative, MixedPeeling and FinitePeeling; the receipt shows zero constants reached in these four. |

All absence statements are bounded to the exact 172-root trace plus the focused four consumers. None is a claim about all repository uses.

## What I checked directly in the 35 bodies

**1. HC46 contract and the selected-leaf consumer**
- The declaration is `theorem original_HC46_exact : HC46ExactContract`. OriginalExactInhabitant imports ActualSelectedComplementAnalyticMoment, so this is the very constant that `selected_leaf_HC46_of_exact_PR` takes as `hHC`.
- `selected_leaf_HC46_original` is the term `selected_leaf_HC46_of_exact_PR T f hPR hi hp4 hpDyadic original_HC46_exact`: the same T, the same f, `d = 2*h` with `hEven := rfl`, and no hHC binder.
- The failed-zoom variant produces `hPR` at `2e` for that same `rankImageBoolean (leafMatchBit T f)`:
  - The chain is `selected_leaf_failed_zoom_PR` → `actual_leaf_failed_zoom_gives_nominal_pseudorandom`, which rewrites through `leafMatchBit_fun_eq_matchingLeafSet`, → `failed_zoom_gives_exact_bound` (using `pairOfGlobal Q W hQW f`, i.e. the f-specific pair) → `exact_zoom_implies_nominal_pseudorandom`.
  - Premises kept explicit: `r < 2h`, `0 ≤ e`, `hfail`.

**2. HC46 body: unrestricted η, zero density, factor 2**
- **Case i = 0:** handled by `hc46_rank_zero_exact`, with both branches present (η ≤ 1, and η > 1 using norm ≤ 1 ≤ η^α).
- **η ≥ 0** is derived from `uniformMean_indicator_nonneg` together with `boolean_mean_le_of_exact`.
- **Case δ = min η 1 = 0:** gives `booleanIndicatorComplex b = 0` (via `original_HC46_boolean_zero_of_energy_zero`), hence norm 0.
- **Case δ > 0:** the chain is
  1. `exactPR_to_actual_LqGlobal` (the parameter is literally `(min eta 1)^(1-1/p)`);
  2. restrict to order ≤ i via `hQ.trans hi`;
  3. `manuscript_A22_actual`;
  4. `actual_A18_original_global` at r = i, with `a18BudgetScale i i = 2^(10i²)·`;
  5. `manuscript_A21_actual`;
  6. `hmomentEq` through `complexRankProjection_boolean_eq`;
  7. the algebra in `original_HC46_moment_density_algebra`: 455 ≤ 500, and exponent p−2+2/p ≥ p−2 with δ ≤ 1;
  8. the p-th root, then δ^α ≤ η^α with α ≥ 0.
- **Non-vacuity:** `exactWholeRestriction n d r` has nominal budget exactly r and fibre `univ` for every r. The premise therefore forces mean ≤ η; the eta = 0, `b ≡ true` case fails it; and eta < 0 is unsatisfiable. Separately, the contract is inhabited by a standard-axiom proof.
- **Not a two-sided result:** `PseudorandomExact` is a one-sided upper bound on density over nonempty fibres at nominal budget exactly r. Zero-row padding (`padRestrictionToBudget`, `pseudorandom_atMost_of_exact`) makes it cover every budget ≤ r.

**3. A22 as originally stated**
- Signature: `{n d j p : Nat}`, `2 ≤ p`, `∃ k, p = 2^k`, globalness at `pConjugate p = p/(p−1)` (a real value).
- **Induction:** strong induction on `level`. The motive is closed over all `n' d' eta g`. `ih (level-1)` is used only on positive-cost parents. Coverage of those parents is exhaustive:
  - if A ≠ ⊥: line `span{x}` with ⊤;
  - if A = ⊥: a codimension-one H ⊇ B, from `a22_exists_order_one_parent`.
- **Zero-cost parents** equal E exactly (`a22_zero_cost_energy`).
- **The dual estimate is never fed an assumed bound.** It runs only after `OriginalActualInfluenceThrough level E` has been proved, via `hclose E le_rfl`. Level 0 is handled separately.
- **Duality:** exact pairing (`a22_projection_pairing`), then `realQNorm_holder_nat_pow`, with the norm taken on the original f via `UpToActualLqGlobal_whole`.
- **Constants:** 810 ≤ 840; `a22_positive_exponent`; 420 → 500.
- **Dependency direction:** A16 → A18 → A20 → A21 → A22 → HC46. Imports are acyclic.

**4. Carrier, counting and normalization**
- **A11** discharges the genuine hS:
  - `a11StrictLowerDegreeIH` is used only at `D − a6Order t < D`;
  - the reindexing is an exact bijection (`a11GlobalInitialEquiv`, `a11NonzeroInitialEquiv`);
  - the A9 partition is exact (`a11GlobalA9SourceEquiv`, `a9AmbientA8PartitionEquiv`);
  - the case split in `a11_actual_fixed_final_saved_charge` covers i > dim A, j > codim B, the out-of-window case (energy 0) and `a9Ambient_fixed_fiber_coarse_charge`;
  - then the A10 saving, the i/j tails, and the W6 bound ≤ 2Q;
  - the W6 step feeds `a7_positive_of_mixed_bound`;
  - `manuscript_A7_actual` uses strong induction.
- **`_horder`** is discharged by the `ho` branch.
- **A8:** the cube is taken once, the square stays inside both the T and S0 averages, and the bound is 6Dk (3Dk proved).
- **A9:** the fibre count is exact, and B ≤ B0 keeps the manuscript variance.
- **DR6:** exact Möbius identity, a partition by the F2 predicate and its complement (so disjointness of F1 and F2 is not needed), and the selector bridge `dr6_complexSelector_iff_actualOrdinary`.
- **A16:** `filteredCarrierFunction_energy_le_A16` has no cost premise.

## Reconciled per-finding table

| # | Origin | Declaration(s) | Prior severity | Disposition | Evidence | Remaining action |
|---|---|---|---|---|---|---|
| 1 | P7 F1 (all lenses); W2 H‑1; W3 retained | `original_HC46_exact`, `selected_leaf_HC46_of_exact_PR`, `selected_leaf_HC46_original`, `selected_leaf_failed_zoom_HC46_original` | HIGH | **RESOLVED (native)** | Same `HC46ExactContract` constant; wrapper terms above; standard root profiles | None for the native scope |
| 2 | Same; W2 N‑3; W1 N1 | `selected_actual_material_moment_bound` | HIGH → material | **OPEN (material).** Instantiation is logically available only as `hHC := original_HC46_exact`; the leaf wrapper cannot be used, because its `LeafTable (2*h)` does not match `c+s` (the contract's `hEven := hsplit` route does fit). No dedicated export exists; AnalyticMoment cannot host one without an import cycle. Tier T2, with T2′ imports. `hSpectral`, `hsel`, `hfail` remain. | AppendMoment pinned unconsumed; not a root | A downstream export, its native profile, and review of the T2′ bodies |
| 3 | P7 proof F2; NC F2 | `HC46ExactContract`, `PseudorandomExact` | HIGH | **RESOLVED.** The proposed counterexample is contradicted by the source. | `exactWholeRestriction_budget/_fibre`, `boolean_mean_le_of_exact`, the inhabitant | None |
| 4 | P7 cx F4; P8 F1/F5 (all lenses) | `padRestrictionToBudget`, `exact_zoom_implies_nominal_pseudorandom`, `smaller_budget_of_exact_r` | Medium | **RESOLVED within the route.** Within the route PR is derived from actual exact-r zoom bounds, never assumed. | Flag averaging; Gaussian divisor > 0; `density_zero_of_fixed_dependent` | Manuscript: nominal versus actual wording |
| 5 | P9 F1–F3 | Same | Medium | **Confirmed as a boundary:** one-sided, budget exactly r (padded), ×2 carried as `2e` | `hR` used only as ≤ r | Do not state as two-sided |
| 6 | P8 F6 | `smaller_budget_of_exact_r`, `raw_left_rows_lt_free` | Low | **Retained:** strict r < d is needed for `binary_target_half` | Strict half-rank argument | Manuscript must state r < d |
| 7 | P2 F4 / Q2 | `manuscript_A22_actual`, `pConjugate`, `realQNorm_holder_nat_pow` | Medium | **RESOLVED:** no real-p interpolation is required | Signature | Manuscript fidelity of the dyadic-p statement |
| 8 | P2 non-claims | `OriginalActualInfluenceThrough` (includes order 0) | Low | **Internally consistent;** every producer discharges the order-0 case | `a22_zero_cost_energy`, `a20_three_degree_global` | Manuscript definition check |
| 9 | P4 F1/F2; cx F1 | `a11_original_weighted_mixed_bound`, `manuscript_A7_actual` | Medium | **RESOLVED** | Point 4 above | None |
| 10 | P4 F3; P5 F4/N8 | `a7_a9_preceding_*`, `a7_a9_zero_parent_family_le`, `a9_initial_datum_card`, `a9_fiber_triple` | Medium | **Resolved within the bounded scope.** Tier T2; not credited. | A11 text; legacy-consumption receipts; the reached A9InitialGraph constants are only `F` and `a9_quotientFintype` (a subsingleton instance) | No absence claim beyond the trace |
| 11 | P5 N1 | `a8_output_q_le_actual_predecessor_sum` `_horder` | Low | **RESOLVED** | A11 `ho` | None |
| 12 | P5 F9; P6 Q1–3 | DR6Moment, DR6Incidence | Medium | **RESOLVED** | Partition, selector bridge, Parseval | Manuscript: constants 162, 6D², 7D(i+j), 31/225, and the proof route (Gram–Cauchy versus 81) |
| 13 | P2 F1 | `a18BudgetScale`, `a18_top_contribution_le_nine512`, `a18_lower_absorption` | Integration | **RESOLVED** | InductionBounds body | None |
| 14 | P2 F2 | `filteredCarrierFunction_energy_le_A16` | Integration | **RESOLVED:** no cost premise | A16Final signature | None |
| 15 | W3‑M1; W2 N‑4 | Unselected imports; reached legacy-module constants | Medium | **Resolved within the bounded scope** | Coverage receipt: four modules with zero reachable constants; `project_modules_outside_selection: []`; enumerated reached constants | The receipt is not independently recomputed |
| 16 | P8 F1 | Five "UNCOMPILED" banners | Medium | **Resolved as provenance:** the five files are in the 319 closure, so the banners are stale and carry no weight either way | Banner-membership receipt | Clean up before the render gate |
| 17 | P8 F4 | `binary_affine_target_*` aliases | Low | **Not credited**; tier T2 | Trace receipt | None |
| 18 | P1 F1 | `a22_parent_from_order_one_coordinate` | Low | **Retained:** a root, but conditional on `hderived` and unused by the line/hyperplane path; its docstring overclaims | ParentFactorization | Fix the docstring; cite only as conditional |
| 19 | P7 cx F2; NC F3 | `Spectral47ExactContract` (cutoff choice) | Medium | **OPEN** | Unproved | Prove it, or keep it as an explicit premise |
| 20 | P7 F4; NC F4 | `selected_actual_analytic_rhs`, the HC46 constant with η = 2e | Medium | **OPEN (numeric NO)** | No usefulness theorem exists | Parameter analysis |
| 21 | P6 N7 | `AllAmbientInverse` | Info | **OPEN (robust8S)** | Unproved Prop | Out of this milestone |
| 22 | P1 F3; P5 N7 | `set_option diagnostics true`, `respectTransparency false`, `with_unfolding_all` | Low | **Elaboration only.** Zero owned warnings ≠ zero total warnings. | Native receipt | Inherited warning debt; disposition of info messages |
| 23 | Stale comments (A11 "run 56", A8 "frozen 46/56", DR6 "uncompiled/open", `hc46_rank_zero_exact` "remaining") | Various | Low | **No weight either way** | — | Clean up |
| 24 | Native-evidence wording | `"standard_axiom_profiles": true` | — | **CORRECTED:** scope is the 172 roots and their closures only | See Evidence tiers | Scope the flag in all records |
| 25 | P4 NC note 5 | Q upper bound | Low | **Partial:** `a12_Q_le_influence_mass` and `manuscript_A12_actual` are roots used on the A19/A21 path | Native stdout | Manuscript match for Q |

## Proved, incomplete, contradicted and unsupported conclusions

**Proved** (on the native receipts, pinned Init/Mathlib/Batteries trust, and the prior packet reviews):
- `original_HC46_exact` holds for unrestricted real η.
- `manuscript_A22_actual` holds for natural dyadic p ≥ 2 with real q = p/(p−1), over all finite spaces.
- `selected_leaf_HC46_original` holds, and the failed-zoom version holds with parameter 2e for the same T and f.
- The A7/A11, A8/A9, DR6, A16, A18, A20 and A21 transitions hold as described above.

**Incomplete:**
- An hHC-free material-moment declaration, with a profile.
- Spectral47.
- Useful numeric NO bounds.
- Manuscript fidelity of definitions and constants.
- Material imports outside the 170.

**Contradicted:**
- The P7 vacuity counterexample.
- "Real-q A22 needs interpolation", as an obligation.
- "All constants in the 319 modules have standard profiles."
- The stale docstrings claiming the work is uncompiled or still open.

**Unsupported:**
- Two-sided pseudorandomness.
- That `hfail` can be met with a useful e.
- Plugging the leaf wrapper directly into the material consumer.
- Zero total warnings.
- Absence of the legacy helpers across the whole repository.
- Any reduction, runtime, learning, upstream, fresh-checkout or provider acceptance.

## Required bodies or profiles that are missing

For the native scope: none.

For material readiness:
- A dedicated export, for example `selected_actual_material_moment_bound_original`, defined in a module that imports OriginalExactInhabitant, together with its fresh `#print axioms`.
- Complete bodies for, and review of: ActualSelectedSpectralParameters, ActualFiniteMomentLpBounds, ActualAppendFourierCrossLevelOrthogonality, ActualRankImageRightBasisInvariance, ActualFixedFunctionalBinaryMatrixMoment, ActualFixedFunctionalAppendOperator, ActualComplementCoordinateMassBridge, MatrixGrassmannIdentity, and the Cmmsa / Tagged / OrdinaryStar modules.
- AppendMoment, re-reviewed as consumed material.

## Bounded safe claim

> On the qualified Full89 native evidence (seven zero exits; 172 roots with standard transitive profiles; 319 pinned sources; 566 unchanged objects), and with explicit trust in the pinned kernel and libraries:
> - the universal theorem `original_HC46_exact : HC46ExactContract` holds for unrestricted real η;
> - original A22 holds for natural dyadic p ≥ 2 with real conjugate q;
> - both are applied, without an hHC premise, to the same pre-drawn selected leaf T and functional f;
> - the failed-zoom route yields the one-sided nominal bound `PseudorandomExact r (2e)` under r < 2h and e ≥ 0.
>
> No material-moment, Spectral47, numeric, reduction, runtime, learning or manuscript result is claimed.

## Remaining to-do list

1. Write the hHC-free material export downstream of OriginalExactInhabitant, compile it natively, run `#print axioms` on it, and review the T2′ bodies.
2. Prove Spectral47, or keep it as an explicit premise and settle the cutoff choice.
3. Do the numeric-NO and parameter usefulness analysis (low-level prefactor against η^(m−½); high-level energies; achievability of e).
4. Check manuscript fidelity:
   - HC4.6 statement and constants (500, (p−2)/p, ×2);
   - nominal versus actual exact-r; r < d;
   - order-0 influence; the A22 dyadic-p form;
   - DR6 constants and proof route; the Q definition and its upper bound;
   - render and novelty; citations.
5. Close the remaining source/star/robust8S lanes (including `AllAmbientInverse`), the encoded reduction, and the runtime/learning gates.
6. Validate upstream builds and bridges, and replay from a fresh checkout.
7. Dispose of the inherited warning baseline debt and the diagnostics info output.
8. Clean up the stale banners and docstrings, and scope `standard_axiom_profiles` to the 172-root closure in every record.
9. Run the final full-scope provider gates. This review cannot certify the full manuscript.
