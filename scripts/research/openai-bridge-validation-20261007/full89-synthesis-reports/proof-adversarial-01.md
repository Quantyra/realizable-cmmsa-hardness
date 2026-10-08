# Full89 cross-partition integration synthesis: proof-adversarial review

## Verdicts

These are two separate verdicts on two separate scopes.

**1. Selected-leaf and native integration: GO-WITH-NOTES.**
- **Scope.** The original natural-dyadic-p A22 with real conjugate q, the universal unrestricted-η HC46, and the two selected-leaf consumers on the same predrawn T and f.
- **Basis.** I read all required bodies and skipped none. No HIGH finding remains open inside this scope. Every HIGH question raised by an earlier window is now either resolved from source or turned into an explicit non-claim, as the table below shows.
- **What this is not.** It is not acceptance, and it gives no milestone sign-off.

**2. Full material-moment and manuscript readiness: INCOMPLETE. No readiness is supported.** The following remain open:
- an hHC-free material-moment declaration;
- Spectral47;
- a useful numeric NO bound;
- source, star and robust8S;
- reduction, runtime and learning;
- upstream builds and bridges;
- warning-baseline disposition and a fresh checkout;
- manuscript fidelity, rendering, novelty and citations;
- the final provider gates.

This review cannot certify the manuscript.

**How the review was done.** No tools, no writes, no Lean or Lake runs, and no subagents. Source identity comes from the supplied pins and native receipts; I did not recompute any hash. I cite by declaration name, not line number.

## Coverage

| Item | Inspected | Skipped |
|---|---|---|
| Complete cross-partition bodies supplied in this invocation | **35** | **0** |
| Window integration reports (3 windows × 3 lenses) | 9 | 0 |
| Complete-body packet reports (9 packets × 3 lenses) | 27 | 0 |
| Remaining selected bodies (170 − 35 = 135) | Not re-read. I reused their prior three-lens reviews only under their exact pinned source, dependency and native identities. | — |

The 35 bodies are:
- **A22/HC46 and consumer:** A22ParentFactorization, A22OriginalInduction, OriginalExactInhabitant, OriginalApplication, AnalyticMoment, BinaryMatrixFourier, ActualBinaryMatrixHC46, RealQNorm, RealQTransport.
- **Leaf label and matrix lift:** LeafLabelRankImageAlignment, FixedFunctionalMatrixLift, MatrixLiftNominalDirectComparison, MatrixLiftExactBudgetZoom.
- **A11 and DR6:** A11WeightedAggregate, DR6Convolution, DR6Incidence, DR6Mobius, DR6Moment, DR6SignMoments.
- **A18 to A21:** A18OriginalGlobalInduction, A18InductionBounds, A20SquareGlobalness, A21DyadicMoment.
- **A7, A8, A9:** A7T1Transfer, A7WeightedPredecessor, A8AmbientAssembly, A8AveragedAssembly, A8AveragedTransport, A8Endpoint, A9AmbientFiber, A9AmbientReindex.
- **A16:** CommonA16, FourierA16, FullA16Assembly, FullA16Final.

## Correction to earlier reports: axiom evidence is not module-wide

The fresh `#print axioms` output covers **the 172 requested roots and the constants each one transitively reaches**. It does **not** show that every declaration in the 319 compiled modules has a standard profile. Compiling a module only shows that it elaborated without errors.

Earlier statements that need this narrowing:

- **Packet 1, window 1 and other reports** imply that compiled-and-pinned modules carry standard profiles throughout. They do not.
- **Window 1 (proof lens)** lists `pseudorandom_atMost_of_exact` among dependencies covered by the root profiles. It is not on the `original_HC46_exact` path as supplied: that path uses `boolean_mean_le_of_exact`, `binary_hc_rankZero_exact` and `exactPR_to_actual_*`. It may be reached through `exactPR_to_actual_normSqGlobal` in BooleanGlobalness, but the supplied evidence does not list per-constant membership. Treat it as **unverified**.

Declarations in the inspected bodies with **compile evidence only and no fresh profile**:
- `selected_actual_material_moment_bound`
- `selected_actual_HC_spectral_moment_bound`
- `matching_center_mass_eq_grassmann_beta`
- `selected_actual_source_dimension_bound`
- the unused private helpers in A8AveragedTransport
- the `*Checks` harness files
- `nominal_score_mean_eq_raw_dim`

`dr6_actual_complex_fourth_moment_over_162_le` is probably reached, via A11 → `a7_positive_of_mixed_bound` → `manuscript_A6`. That is my inference, not an enumerated fact.

Zero owned warning headers is consistent with no `sorry` in the owned modules, and I found no `axiom` declaration in the inspected text. Neither fact substitutes for a per-declaration profile.

## Reconciled findings

| ID (origin) | Sev. | Declarations | Disposition | Evidence | Remaining action |
|---|---|---|---|---|---|
| **H1** (P7 all lenses, W2 H-1, W3) — hHC in the consumer | HIGH → **Resolved** for the selected leaf; **Medium non-claim** for the material moment | `original_HC46_exact`, `HC46ExactContract`, `selected_leaf_HC46_original`, `selected_leaf_failed_zoom_HC46_original`, `selected_actual_material_moment_bound` | The universal theorem is typed exactly as the single `HC46ExactContract` defined in AnalyticMoment, which OriginalExactInhabitant imports and opens. Both selected wrappers pass it as `hHC` with no added premise: same T, same f, `hEven := rfl`, η = 2e. The material bound could take it at the type level (it is used only at `b = selectedF Tc fc`). | Source of all four files. Both wrappers have standard root profiles. | Material export: write `…_original` that supplies `hHC := original_HC46_exact`, get its native profile, and review its unpinned support modules (SelectedSpectralParameters, FiniteMomentLpBounds, AppendFourierCrossLevelOrthogonality, RankImageRightBasisInvariance, FixedFunctionalBinaryMatrixMoment, the Cmmsa/Tagged/OrdinaryStar families). It would still depend on `hSpectral`, `hsel` and `hfail`. |
| **H2** (P7-F2, W2 H-2) — vacuous or refutable contract; η < 0 | HIGH → **Resolved** | `exactWholeRestriction`, `exactWholeRestriction_fibre/_budget`, `boolean_mean_le_of_exact` | For every r, the whole space is a nonempty restriction of nominal budget exactly r. So PR implies mean ≤ η, which forces η ≥ 0. Negative η makes the premise unsatisfiable, so a negative `rpow` base is never reached. The contract has a standard-axiom inhabitant. | BinaryMatrixFourier; OriginalExactInhabitant derives `heta` | None in scope. |
| **H3** (P2-F4, W2) — real-q A22 interpolation | Medium → **Resolved** (scope) | `manuscript_A22_actual {n d j p : Nat}`, `pConjugate`, `realQNorm_holder_nat_pow`, `pConjugate_holder` | p is a natural dyadic number ≥ 2. q = p/(p−1) is an exact real. Hölder is natural-powered and keeps a true real-q norm. A21 is used only at dyadic p. No interpolation is needed or claimed. | A22OriginalInduction, RealQNorm | Manuscript statement fidelity (open). |
| **R1** — zero-density and δ branches | — **Verified** | `original_HC46_exact` | δ = min(η, 1). δ = 0 gives f = 0 and norm 0 ≤ RHS. i = 0 is handled by `hc46_rank_zero_exact` (both η ≤ 1 and η > 1). Rechecked: coefficient 455 ≤ 500·i²p²; exponent p − 2 + 2/p ≥ p − 2 applied in the right direction; final δ ≤ η with a nonnegative exponent. | OriginalExactInhabitant, ActualBinaryMatrixHC46 | — |
| **R2** — A22 induction and parents | — **Verified** | `manuscript_A22_actual`, `a22_positive_parent_from_lowerIH`, `a22_dual_energy_of_influences`, `a22_zero_cost_energy` | Strong induction is over all spaces and uses only `ih (level−1)`. The dual estimate is applied only after `hclose E` proves the influence premise. Parents are covered exhaustively (line `span{x}` or a hyperplane above B), with exact additive cost and the witness factor 2^(6j). | A22ParentFactorization, A22OriginalInduction | — |
| **R3** — `a22_parent_from_order_one_coordinate` | Low **retained** | — | A root, but conditional on `hderived`, and not called on the A22 path. Its docstring overclaims. | Source | Do not credit it as unconditional. |
| **R4** (P8-F1/F5, P7cx-F4, P9 F1/F2) — nominal vs actual exact budget; one-sided; ×2 | Medium → **Resolved in route**; claim boundary kept | `padRestrictionToBudget*`, `pseudorandom_atMost_of_exact`, `exact_zoom_implies_nominal_pseudorandom`, `smaller_budget_of_exact_r`, `fixed_residual_mean_le_two`, `density_zero_of_fixed_dependent`, `failed_zoom_gives_exact_bound` | PR is **derived** from the actual exact-r zoom bound by flag averaging (a = r − codim; Gaussian divisor > 0; empty refined zooms contribute 0). Guards are strict: r < d gives b < k, which gives `binary_target_half`. Dependent fixed columns give density 0. The result is a one-sided upper bound with factor exactly 2e. | MatrixLift×2, ActualFixedFunctionalMatrixLift, ActualBinaryMatrixHC46 | Manuscript wording; whether a useful e exists (numeric-NO). |
| **R5** (P8-F6, P9-F3) — `r < d` | Low **retained** | `hrd` | Required for the strict half-rank bound. r = d is not covered. | Source | — |
| **R6** (P4-F1/F2, W2) — A11 discharge of hS; overlap | Medium → **Resolved** | `manuscript_A7_actual`, `a11_original_weighted_mixed_bound`, `a11GlobalInitialEquiv`, `a11GlobalA9PartitionEquiv`, `a11_actual_fixed_final_saved_charge`, `a11_full_finite_ij_tail` | Genuine strict, simultaneous lower-degree IH. Exact initial-data bijection and A9 partition. Costs 2^(6Dk), 2^(3D(i+j+k)) and 2^(24Dt) each charged once. Orders above D are zero by proof. Exhaustive case split (`i > dim A` empty, `j > codim B` empty, outside the window zero energy). `_horder` is supplied by `ho`. Re-derived: A10 saving, tails (1 + 31D ≤ 32Dk), and the W6 step. | A11 source | — |
| **R7** (P4-F3, P5-F4) — legacy A7/A9 helpers | Medium → **Resolved (bounded)** | `a7_a9_preceding_*`, `a7_a9_zero_parent_family_le`, `a9_initial_datum_card`, `a9_fiber_triple` | Not referenced in A11, A8Endpoint or A9Ambient*. The bounded trace lists A9InitialGraph's reached constants as only `F` and `a9_quotientFintype`, a Fintype instance (Subsingleton, harmless). The reached A7Transfer constants include no degenerate parent-family helper. | Coverage JSON; source | No absence claim for the whole repository. |
| **R8** (W3-N1) — imported modules outside the 170 | Medium → **Resolved (bounded)** | A9ActualFiber, CommonDerivative, MixedPeeling, FinitePeeling | Zero reached constants in each. `consumed_project_modules_outside_selection = []`. | Coverage JSON | — |
| **R9** (P5-F9, P6 Q1–3, W2) — DR6 F1/F2, signed incidence, normalization | — **Verified** | `dr6_actual_complex_fourth_moment_over_162_le`, `dr6_actual_complex_convolution_partition`, `dr6_f2_a5SquareCoefficient_eq_original_obstruction_sum`, `dr6_actual_f1_total_energy_le` | Exact partition by P versus ¬P, with the complement injected into F1. Exact Möbius indicator from the actual q-Pascal recurrence. Kernel side via a genuine dual-annihilator bijection. The selector equals `DR6OrdinarySelected`. Constants 2^(6D²), 7D(i+j) and 31/225 are valid, and the /162 is slack (the formal route gives a factor of 2). | DR6 ×5 | Manuscript constants and proof-route text. |
| **R10** (P2-F1/F2, W2) — A18/A20/A21 constants and direction | — **Verified** | `a18BudgetScale = 2^(10Dr)·eps`, `a18_top_contribution_le_nine512`, `a18_lower_absorption`, `a20_three_degree_global`, `a21_dyadic_strong` | Dependency direction A16 → A18 → A20 → A21 → A22 → HC46, acyclic by imports. A16 is cost-free. Budgets 41D² and 196D² check. The A21 recurrence 200q ≥ 98q − 82 holds. | Source | — |
| **R11** (non-claims P2) — order-0 influence | Low **retained** (fidelity) | `OriginalActualInfluenceThrough` | Includes the A = ⊥, B = ⊤ carrier. Every producer discharges it (A16 in A20; the zero-cost identity in A22). | Source | Check against the manuscript. |
| **R12** (P2-F2) — A16 | — **Verified** | `filteredCarrierFunction_energy_le_A16` | Premises are support plus actual up-to-D globalness only. Zero-carrier branch handled. Low ranks annihilated. Residual ranks are orthogonal by Parseval, not by assumption. (D + 1)·2^(10D²) ≤ 2^(11D²). | A16Final, A16Assembly, CommonA16, FourierA16 | — |
| **R13** — A8/A9 contracts | — **Verified** | `a8_output_q_le_actual_predecessor_sum`, `a9AmbientA8PartitionEquiv`, `a9_ambient_fiber_card`, `a8_supported_graph_charge` | The guard literally equals the A9 side conditions. The square stays inside both averages. The cube is taken once. 6Dk is valid with slack (3Dk is proved). | Source | Manuscript exponent fidelity. |
| **R14** (P3 N1/N3) — T1 orientation and offset 0 | — **Resolved** | `hactive_iff` (by `rfl`), `t1TypedW6_eq_actual` | `typedW6Precedes` is definitionally rank-additivity in the stated orientation. The 0 is the affine base; T is carried inside the coordinate. | Source | — |
| **N1** — stale status text | Low | DR6Moment ("uncompiled"), DR6Incidence ("remain open"), DR6Mobius header, `hc46_rank_zero_exact` ("remaining"), AnalyticMoment header, A11 and A8Averaged* "accepted… run 46/56", `carrierFibreQNorm_hyperplane_coordinate` ("line") | Carries no evidential weight either way. | — | Fix before render. |
| **N2** — elaboration options | Info | `respectTransparency false`, `with_unfolding_all`, raised heartbeats | Affect the elaborator only; the kernel re-checks. | — | Note for replay. |
| **N3** — warnings | Open | — | Zero owned warnings and zero inherited regressions are not zero total warnings. The inherited baseline debt is open. | Audit JSON | Disposition gate. |

## Missing evidence before broader claims

1. A dedicated hHC-free material-moment declaration, with its native profile and a review of its unpinned support modules.
2. Per-constant membership of the trace for unenumerated dependencies (`pseudorandom_atMost_of_exact`, the DR6 final theorem), if those are to be credited as axiom-profiled.
3. The manuscript text for HC4.6, A22, the influence definition and every constant: 500, 420, 2e, 162, 6D², 7D(i+j), 31/225, 41D², 196D², 6Dk, 3D(i+j+k), 11D².
4. Spectral47 proof; a useful numeric e and η.

## What can safely be claimed

The following holds under the pinned Init/Mathlib/Batteries/kernel trust, the qualified native receipts (seven zero exits, 172 standard root profiles, 319 source pins, 566 unchanged objects), and the prior packet reviews of bodies not re-read here:

- The Lean theorem `original_HC46_exact : HC46ExactContract` holds for unrestricted real η. Its premise is non-vacuous at every r and forces η ≥ 0.
- `manuscript_A22_actual` holds for natural dyadic p ≥ 2 with real conjugate q = p/(p−1), over all finite binary matrix spaces.
- `selected_leaf_HC46_original` applies HC46 to the same predrawn T and f with no hHC premise.
- `selected_leaf_failed_zoom_HC46_original` gives the bound at parameter 2e, assuming `hfail`, r < 2h and e ≥ 0. The underlying `PseudorandomExact` is a one-sided nominal-budget density upper bound.

**Must not be claimed:**
- a material-moment, Spectral47 or numeric-NO result;
- reduction, runtime or learning results;
- upstream, fresh-checkout or provider gates;
- two-sided pseudorandomness;
- manuscript fidelity, rendering or novelty;
- zero total warnings;
- that legacy helpers are absent from the whole repository;
- that library bodies were newly reviewed;
- any full-manuscript verdict or acceptance.

## Remaining work

1. Export and natively profile an hHC-free material-moment theorem; review its unpinned support modules.
2. Prove Spectral47. Establish a useful e in `ExactBudgetZoomBound` and the numeric NO bound.
3. Source, star and robust8S (`AllAmbientInverse` is unproved). Encoded reduction, runtime and learning.
4. Upstream builds and bridges; fresh-checkout replay; final provider gates.
5. Warning-baseline disposition (inherited debt).
6. Manuscript fidelity of the definitions and constants in "Missing evidence" item 3. Remove the stale banners and docstrings in N1. Rendering, novelty and citations.
7. Optionally, enumerate per-constant trace membership for any dependency to be credited by name.
