# Full89 cross-partition integration synthesis: complexity lens, final

## Verdicts

| Scope | Verdict |
|---|---|
| **Selected-leaf / native integration** (original A22 with natural dyadic p and real conjugate q; unrestricted-η HC46; the same selected leaf consumer) | **GO-WITH-NOTES, bounded.** All 35 required bodies were inspected and none skipped. No HIGH question about this milestone is left open. This is not acceptance. |
| **Full material-moment / Spectral47 / numeric-NO / manuscript readiness** | **INCOMPLETE. Not certifiable.** Required declarations, profiles and bodies are missing (§5), and several gates are open by construction. |

I used no tools, wrote no files, ran no Lean or Lake, and spawned no subagents. I compared source hashes as labels against the all170 pins only; I did not recompute them. Native facts (7 stage exits of 0, 172 root profiles, 319 source pins, 566 unchanged objects) come from the qualified receipts. Init, Mathlib and Batteries are trusted at their pinned versions and were not reviewed. References are by declaration name.

## 1. Coverage

| Set | Count | Status |
|---|---|---|
| Window 1 bodies: ParentFactorization, A22OriginalInduction, OriginalExactInhabitant, OriginalApplication, AnalyticMoment, BinaryMatrixFourier, ActualBinaryMatrixHC46, RealQNorm, RealQTransport, LeafLabelRankImageAlignment, FixedFunctionalMatrixLift, MatrixLiftNominalDirectComparison, MatrixLiftExactBudgetZoom | 13 | inspected |
| Window 2 bodies: A11WeightedAggregate, DR6Convolution, DR6Incidence, DR6Mobius, DR6Moment, DR6SignMoments, A18OriginalGlobalInduction, A18InductionBounds, A20SquareGlobalness, A21DyadicMoment | 10 | inspected |
| Window 3 bodies: A7T1Transfer, A7WeightedPredecessor, A8AmbientAssembly, A8AveragedAssembly, A8AveragedTransport, A8Endpoint, A9AmbientFiber, A9AmbientReindex, CommonA16, FourierA16, FullA16Assembly, FullA16Final | 12 | inspected |
| **Cross-partition bodies in total** | **35 / 35** | **0 skipped** |
| Window reports (3 windows × 3 lenses) | 9 | read |
| Packet reports (9 packets × 3 lenses) | 27 | read |
| Remaining selected bodies | 135 | reused only under their exact pinned source and native identities, not re-inspected |

## 2. Native statements checked as stated (not narrowed)

### `manuscript_A22_actual`
- **Statement:** for `{n d j p : Nat}` with `2 ≤ p` and `∃k, p = 2^k`, from `UpToActualLqGlobal j (pConjugate p) eps f` it concludes `OriginalActualInfluenceThrough j (2^(500 j² p)·eps²) (complexRankProjection j f)`.
- **q is real.** `pConjugate p = p/(p−1)`; at p = 4 it is 4/3.
- **eps is unrestricted.** Its nonnegativity is derived from the order-0 whole fibre via `UpToActualLqGlobal_parameter_nonneg`.
- **Induction.** Strong induction on `level` over all `n' d' eta g`. Positive-cost parents use only `ih (level−1)`, through `a22_positive_parent_from_lowerIH`.
- **Parent coverage is exhaustive:**
  - A ≠ ⊥: the domain line `span{x}` with U = ⊤ and an arbitrary inner Q.
  - A = ⊥ with positive cost: a hyperplane H ⊇ B.
  - Both branches use exact additive cost (`relative_endpoint_cost_add`). The witness factor 2^(3j) contributes +6j.
- **The dual estimate never runs on an assumed premise.**
  - Zero-cost parents equal E exactly (`a22_zero_cost_energy`).
  - In the branch B < E, `hclose E le_rfl` proves the influence bound first, and only then is `a22_dual_energy_of_influences` applied.
- **Duality step.** It uses the exact pairing (`a22_projection_pairing`) and `realQNorm_holder_nat_pow`, which is natural-power Hölder against a genuine real-q norm.
- **Exponents.** I re-checked 800j²m² + 10j²(m−1) ≤ 810j²m² ≤ 420j²p·m and 500(j−1)²p + 6j ≤ 500j²p.
- **No interpolation to arbitrary real p is claimed or needed.**

### `original_HC46_exact : HC46ExactContract`
- **Type identity.** The declared type is literally the closed `Prop` from `ActualSelectedComplementAnalyticMoment`. OriginalExactInhabitant imports that module, so this is the same constant.
- **No added premise.** There is no hHC, η ≤ 1 or basis-invariance premise.
- **Branch i = 0:** `hc46_rank_zero_exact`, which covers both η ≤ 1 and η > 1.
- **Branch i ≥ 1:**
  - η ≥ 0 is derived; δ = min η 1.
  - δ = 0 forces f = 0, so the norm is 0.
  - Otherwise the chain is `exactPR_to_actual_LqGlobal` (parameter `(min η 1)^(1−1/p)`, restricted to order ≤ i via `hi`) → A22 → A18 at (i, i) with scale 2^(10i²) → A21.
  - The density exponent is p−2+2/p ≥ p−2, applied in the correct direction because δ ≤ 1.
  - The coefficient is ≤ 455i²p² ≤ 500i²p². The final step uses δ ≤ η with an exponent ≥ 0.

### Same selected leaf consumer
- `selected_leaf_HC46_original` is literally `selected_leaf_HC46_of_exact_PR T f hPR hi hp4 hpDyadic original_HC46_exact`, with the same predrawn `T`, the same `f`, and `d = 2h` by `rfl`.
- The failed-zoom wrapper derives `hPR` at parameter `2e` for the same `T` and `f`:
  - path: `selected_leaf_failed_zoom_PR` → `actual_leaf_failed_zoom_gives_nominal_pseudorandom` → `failed_zoom_gives_exact_bound` → `exact_zoom_implies_nominal_pseudorandom`;
  - premises kept: `r < 2h`, `0 ≤ e`, `hfail`.

### Exact budget mechanics

**Nominal budget is non-vacuous at every r.**
- `exactWholeRestriction n d r` has r zero rows and its fibre is all of `univ`.
- `boolean_mean_le_of_exact` therefore forces η ≥ mean ≥ 0.
- The packet-7 counterexamples (η = 0 with b ≡ true, and η < 0) have unsatisfiable premises.

**Padding and flag averaging.**
- Padding (`padRestrictionToBudget`, giving `pseudorandom_atMost_of_exact`) makes exact-r equivalent to at-most-r on the nominal side.
- Flag averaging (`smaller_budget_of_exact_r`, `sum_refine_flags_constant`) handles smaller actual budgets. The divisor is gaussian(d−q, a−q) > 0, and empty refined zooms contribute 0.

**Guards and edge cases.**
- Strict guards: r < d gives b < k (`raw_left_rows_lt_free`), which feeds `binary_target_half`.
- Dependent fixed columns give density 0 (`density_zero_of_fixed_dependent`).

**Shape of the result.** `PseudorandomExact` is a **one-sided** density upper bound with factor ×2. It is not a two-sided theorem.

### Induction and carrier/counting/normalization transitions (re-read in windows 2–3, re-checked here)
- **A7 (`manuscript_A7_actual`):** strict simultaneous strong induction. hS is genuinely assembled by `a11_original_weighted_mixed_bound`: actual A8 endpoint, exact initial-data bijection, exact A9 partition, saved charge, i/j tails, W6 ≤ 2Q.
- **A18:** a D/r double induction, with constants 9/512 and 1/2 + 2/961.
- **A20:** 2^(196D²).
- **A21:** a dyadic recurrence over all spaces.
- **DR6:** exact Möbius incidence and the F1/F2 partition.
- **Counting:** the A9 fibre count is exact (Gaussian × graph factors); the A8 complement count is cubed once; the T1 count is 2^(dim A·dim W/B).
- **Normalization:** every carrier transport is an `Equiv` sum/card reindexing, with Fintype instances made irrelevant by subsingleton arguments. A1 composition (`a22_A1_composition_energy_eq`) is an equality, not a bound.

## 3. Correction to the axiom-scope claims

- **What the fresh standard-axiom evidence actually covers:** the 172 requested roots and the transitive closures of the constants they reach. It does **not** certify every declaration in the 319 compiled modules.
- **Why compilation is not enough:**
  - Compilation shows that each file elaborated and was kernel-checked.
  - Zero owned warnings rules out `sorry` warnings in owned stages.
  - Neither one bounds the axiom profile of a declaration no root reaches. For example, an explicit `axiom` declaration emits no warning.
- **Specific correction:** the window-3 non-claims sentence on W3-M1 ("These modules sit inside the native 319-file closure, so they are compiled and their axioms are standard") is **incorrect as stated**. The same applies to any prior shorthand of the form "319 modules compile, so standard axioms".
- **Imported-but-unconsumed examples:** these modules are compiled and imported but are pinned `transitively_consumed: false`, so they carry no reachable-declaration axiom evidence:
  - ActualSelectedComplementAppendMoment
  - ActualBinaryMatrixHC46TypedA14Energy and ActualTypedIntrinsicWitnessNaturality (both imported by ParentFactorization)
  - A17FixedSlice, A17DerivativeGlobalTransfer, and all the `*Checks` files
- **`selected_actual_material_moment_bound`** has **no** axiom profile at all.

## 4. Reconciled per-finding table

| ID | Origin | Declarations | Sev. (prior → now) | Disposition | Evidence | Remaining action |
|---|---|---|---|---|---|---|
| R1 | P7 F1 (all lenses); W2 H-1; W3 | `selected_leaf_HC46_original`, `selected_leaf_failed_zoom_HC46_original`, `HC46ExactContract` | HIGH → **resolved for the milestone** | The milestone consumer has no hHC premise. The universal inhabitant has the identical contract type. | Window-1 bodies (Application, Inhabitant, AnalyticMoment); both wrappers are native roots with standard profiles | None for the milestone |
| R1-m | same | `selected_actual_material_moment_bound` | HIGH residual → **open obligation (material gate)** | `original_HC46_exact` can logically fill `hHC` for the same `Tc`/`fc`/`r`/η = 2e. But no export exists: it cannot live in AnalyticMoment (that would be an import cycle), it is not among the 172 roots, it has no profile, and `hSpectral`, `hfail` and `hsel` remain. | AnalyticMoment body; root list | Write a downstream export, get its native profile, review the out-of-170 imports (§5) |
| R2 | P7 F2; nc F2; W2 H-2 | `PseudorandomExact`, `exactWholeRestriction`, `boolean_mean_le_of_exact` | HIGH → **resolved (refuted)** | The contract is non-vacuous at every r and forces η ≥ 0. It is also inhabited with standard axioms, so it cannot be refutable assuming the kernel and pinned libraries are consistent. | BinaryMatrixFourier and Inhabitant bodies | None |
| R3 | P2 F4/Q2 | `manuscript_A22_actual`, `pConjugate`, `realQNorm_holder_nat_pow` | Med → **resolved** | The theorem is stated for natural dyadic p with real conjugate q; no real-p interpolation is required. | A22 and RealQNorm bodies | Manuscript wording check |
| R4 | P8 F1/F5 (3 lenses) | `exact_zoom_implies_nominal_pseudorandom`, `ExactBudgetZoomBound` | Med → **resolved formally; manuscript open** | In the route, PR is derived from actual exact-r zoom bounds and never assumed. | DirectComparison and ExactBudgetZoom bodies | Confirm HC4.6 uses a nominal budget |
| R5 | P7 cx F4; P9 F1; nc F5 | `padRestrictionToBudget`, `pseudorandom_atMost_of_exact`, `smaller_budget_of_exact_r` | Med → **resolved** | Padding and flag averaging cover every lower order | ActualBinaryMatrixHC46 and ExactBudgetZoom bodies | None |
| R6 | P9 F2/F3 | same | Med → **boundary confirmed** | One-sided bound, factor 2e, requires r < d | DirectComparison body | Never describe it as two-sided |
| R7 | P4 F2; P5 Q2/3; cx N1 | A11 chain; `_horder` | Med → **resolved** | Overlap is paid exactly once: A8 2^(6Dk) and A9 2^(3D(i+j+k)). `_horder` is supplied by `ho`. The window split is exhaustive. | A11 body | None |
| R8 | P4 F3; P5 F4 | `a7_a9_preceding_*`, `a7_a9_zero_parent_family_le`, `a9_initial_datum_card`, `a9_fiber_triple` | Med → **resolved, bounded** | Absent from the exact172 trace and the four focused consumers. The only constants reached in A9InitialGraph are `F` and `a9_quotientFintype` (a subsingleton instance). The constants reached in A7Transfer are the genuine injections, counts and conditional lemmas, plus auto-generated `_proof_n` auxiliaries, which carry no data. | Bounded-coverage JSON | This is not an all-repository absence claim |
| R9 | W3 M1 (cx/nc/pa) | A9ActualFiber, CommonDerivative, MixedPeeling, FinitePeeling | Med → **resolved, bounded** | Zero reachable constants in each; `project_modules_outside_selection` is empty | Bounded-coverage JSON | Repository-wide and material scope are not covered |
| R10 | W2 N-3 | ActualSelectedComplementAppendMoment | Med → **retained** | Not consumed; no fresh profile exists for any declaration in it | Pins | Part of the material gate |
| R11 | P2 nc F1; W2 N-1 | `OriginalActualInfluenceThrough` (includes order 0) | Low/Med → **internally resolved; manuscript open** | Every producer proves the order-0 term (A16 in A20; the zero-cost identity in A22) | A18, A20 and A22 bodies | Check against the manuscript definition |
| R12 | P6 N1/N2; W2 N-5/N-6 | DR6 docstrings and route | Low → **retained (documentation and manuscript)** | Docstrings still say "uncompiled" or "open", and describe a Rademacher/81 route while the formal route is Gram–Cauchy (a stronger constant). They carry no evidential weight. | DR6 bodies | Fix docstrings; align the manuscript's proof description |
| R13 | P8 F1 | Five UNCOMPILED banners | Med → **resolved as provenance only** | The files are in the pinned 319 closure; their reached constants are covered by root profiles | Native JSON | Remove stale banners |
| R14 | P8 F4 | `binary_affine_target_*` bridge aliases | Low → **resolved, bounded** | Absent from the trace; the route uses `binary_target_half` | Alias list | None |
| R15 | P1 F1 | `a22_parent_from_order_one_coordinate` | Low → **retained** | A root, but conditional on `hderived` and off the A22 path; its docstring overclaims | ParentFactorization body | Credit only as a conditional lemma |
| R16 | P6 N7 | `AllAmbientInverse`, `first_inverse_witness_of_eightS` | Info → **open (robust8S)** | Not discharged; not on the milestone path | ChangedAmbient8S (packet 6) | robust8S gate |
| R17 | P7 nc F3/F4 | `Spectral47ExactContract`, `selected_actual_analytic_rhs` | Med → **open** | Unproved. Numerical usefulness is not shown: the prefactor is about 2^(4000r²m²) against η^≈m, and the high-level energies are unbounded. Nontrivial `e` in `hfail` is not shown. | AnalyticMoment body | Spectral47 and numeric-NO gates |
| R18 | new (this synthesis) | prior axiom-scope wording | Med → **corrected** | See §3 | Native JSON scope (172 roots) | Restate claims per declaration |
| R19 | new | ParentFactorization imports TypedA14Energy and IntrinsicWitnessNaturality | Info | Imported but unconsumed; compiled, with no reachable axiom evidence and no credit | Pins | None |
| R20 | P1/W1 | stale `hc46_rank_zero_exact` docstring and A11/A8 "accepted at run 46/56" headers | Low | No evidential weight in either direction | Bodies | Fix the documentation |
| R21 | Receipts | Warnings | Open | Zero owned warnings and zero inherited regressions are established. That is not zero total warnings; the inherited baseline debt remains. | Qualified audit | Disposition of the warning baseline |

**No HIGH item is unresolved for the native milestone.** R1-m is a material-gate obligation, not a milestone defect.

## 5. Missing evidence required for the material and full verdicts
1. **A dedicated hHC-free material declaration.** It must live in a module downstream of OriginalExactInhabitant, instantiate `selected_actual_material_moment_bound (hHC := original_HC46_exact)` on the same `Tc`/`fc`/`r`/2e, and come with its fresh native axiom profile.
2. **Reviewed bodies for AnalyticMoment's imports outside the 170:**
   - ActualSelectedSpectralParameters
   - ActualFiniteMomentLpBounds
   - ActualAppendFourierCrossLevelOrthogonality
   - ActualRankImageRightBasisInvariance
   - ActualFixedFunctionalBinaryMatrixMoment and ActualFixedFunctionalAppendOperator
   - MatrixGrassmannIdentity
   - ActualComplementCoordinateMassBridge
   - the Cmmsa, Tagged and OrdinaryStar families, SamplerParameters and StarFixedRhoDimensionGuard
   - plus confirmation that AppendMoment is consumed.
3. **A proof inhabiting `Spectral47ExactContract`** at the cutoff that is actually instantiated (`analyticSourceHeightFloor`/`hsel`).
4. **A proof that `hfail` holds with a useful `e`,** and numeric-NO bounds for `selected_actual_analytic_rhs`.
5. **Manuscript texts** for HC4.6 (nominal or actual exact-r premise; constants 500 and (p−2)/p), for A7–A22 (constants 100, 24, 63, 31, 162, 6D², 7D(i+j), 31/225, 41, 196, 200, 420→500), the order-0 influence definition, and the DR6 proof route.
6. **Per-declaration profiles** for any claim about declarations outside the 172-root closure.
7. **Total-warning evidence, a fresh-checkout replay, and the final-provider records.**

## 6. Bounded safe claim
Under the qualified native receipts, the pinned trust in kernel and Init/Mathlib/Batteries, and reuse of the 135 unchanged prior-reviewed bodies, the following is established:
- **`original_HC46_exact`** proves the unchanged exact-budget Boolean `HC46ExactContract`:
  - it holds for every real η and is non-vacuous, but has content only for η ≥ 0, because negative η makes the premise unsatisfiable;
  - it takes no hHC, η ≤ 1 or basis-invariance premise.
- **`manuscript_A22_actual`** proves the original A22 for natural dyadic p ≥ 2 with real conjugate q, over all finite binary-matrix spaces, by strict lower-level induction.
- **The selected wrappers.**
  - `selected_leaf_HC46_original` applies the contract to the same predrawn leaf `T` and functional `f` with no added premise.
  - `selected_leaf_failed_zoom_HC46_original` gives the bound with parameter 2e, conditional on `r < 2h`, `0 ≤ e` and `hfail`, using a one-sided nominal-budget PR derived from actual exact-r zoom bounds.
- **The supporting chain** A7/A11, A8/A9, DR6, A16, A18, A20 and A21 holds with the constants re-verified above.

**Not claimed:**
- hHC-free material-moment acceptance;
- Spectral47 or numeric NO;
- source/star/robust8S, encoded reduction, runtime or learning;
- upstream builds or bridges, a fresh checkout, or the final provider;
- manuscript fidelity, render, novelty or citations;
- zero total warnings;
- that legacy helpers are absent repository-wide;
- standard axioms for unreached declarations;
- any full-manuscript verdict.

## 7. Remaining to-do
1. Write the hHC-free material export, natively profile it, and review the out-of-170 material imports (§5 items 1–2).
2. Prove Spectral47 at the instantiated cutoff; establish nontrivial `e` and useful numeric bounds.
3. Run the manuscript-fidelity audit: the HC4.6 premise, the A7–A22 statements and constants, the order-0 influence definition, and the DR6 route text.
4. Correct prior axiom-scope wording (§3) and remove the stale docstrings and banners (R12, R13, R20).
5. Close the source/star/robust8S (`AllAmbientInverse`), encoded reduction, runtime and learning, and upstream build and bridge gates.
6. Resolve the inherited warning-baseline debt, run the fresh-checkout replay, and complete the final-provider gates.
7. Complete the manuscript render, novelty and citation checks and the full-scope certification. None of these is authorized or performed by this review.
