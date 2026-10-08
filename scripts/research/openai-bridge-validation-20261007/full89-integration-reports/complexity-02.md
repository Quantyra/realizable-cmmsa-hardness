# Full89 independent integration review, window 2 of 3 (analytic induction and incidence): complexity lens

## Verdict

**GO-WITH-NOTES for this window only.**

- **Scope:** this verdict covers only the 10 complete source files supplied in this window, read against the 27 prior reports and the native evidence. It is not a verdict on the full milestone and not a verdict on the manuscript.
- **Cross-partition integration is still INCOMPLETE.** Both HIGH findings from packet 7 (the HC46 consumer and the contract question) depend on files that are not in this window. Nothing here closes them.
- **How I reviewed:** no tools, no writes, no code, no Lean or Lake runs. I cite declaration names, not line numbers. I did not count lines myself, so the line numbers the Root notes give (550/553/713, 1207–1260) are matched by declaration content only.

## Files inspected in this window (10 of 10, none skipped)

| File | Pin (prefix) | Status |
|---|---|---|
| ActualBinaryMatrixHC46A11WeightedAggregate | B296A5A9 | read in full |
| ActualBinaryMatrixHC46DR6Convolution | CDDF6433 | read in full |
| ActualBinaryMatrixHC46DR6Incidence | 31305E6B | read in full |
| ActualBinaryMatrixHC46DR6Mobius | 6E2CCA4E | read in full |
| ActualBinaryMatrixHC46DR6Moment | 500BF0B2 | read in full |
| ActualBinaryMatrixHC46DR6SignMoments | DAFA4306 | read in full |
| ActualBinaryMatrixHC46A18OriginalGlobalInduction | C4513E43 | read in full |
| ActualBinaryMatrixHC46A18InductionBounds | D583B3DA | read in full |
| ActualBinaryMatrixHC46A20SquareGlobalness | 435873CF | read in full |
| ActualBinaryMatrixHC46A21DyadicMoment | 2B3FE7D9 | read in full |

For the other 160 files I reused the prior three-lens reports, and only on the pinned source, dependency and native identities.

## Evidence I took as given

The following come from the qualified receipts, not from this window:
- 7 native stage exits, all 0.
- All 172 `#print axioms` outputs in the supplied stdout are subsets of {propext, Classical.choice, Quot.sound}. There is no `sorryAx` and no project axiom.
- All 319 source hashes reverified, 566 cache objects unchanged.
- 0 owned warnings and 0 inherited regressions. That is **not** the same as 0 total warnings. The inherited warning-baseline debt is still open, and `set_option diagnostics true` in the A17 files may produce info output.
- Trust in the pinned Init, Mathlib and Batteries libraries is explicit. Those libraries were not reviewed as new proof.

Note: `dr6_actual_complex_fourth_moment_over_162_le` is **not** one of the 172 requested roots. Its standard axiom profile follows only because it sits in the trace closure of the four focused consumers, through packet 6. It was not printed directly.

---

## Findings and what happened to each

### A11 and original A7

**W2-1. A11 genuinely supplies the strict lower-degree `hS`. RESOLVED.** This resolves packet 4 proof F1, packet 4 complexity F1, and packet 5 complexity question 3.

The chain, in order:
1. **The induction hypothesis.** `a11StrictLowerDegreeIH D` quantifies over every e < D and every n, d and g. `a11_actual_mixed_fourth_le_output_q` applies it at `D − a6Order t` (strictly less than D, because `hpos` holds) to `a7OutputBinary t T f`, which lives on a different matrix space. That is why the hypothesis has to be simultaneous across spaces, and it is.
2. **The A8 step.** `a11_actual_mixed_fourth_le_actual_final_sum` composes with `a8_output_q_le_actual_predecessor_sum`.
3. **The full chain.** `a11_weighted_mixed_sum_le_actual_initial_sum` → `a11_weighted_actual_A9_partition` (an exact equality) → `a11_actual_final_fibers_le_post_tail_energy` → `a11_all_actual_final_energy_terminal` → `a11_original_weighted_mixed_bound`. This yields exactly `2^(100D²)·2^(1−31D)·Q`, the shape `a7_positive_of_mixed_bound` requires. Packet 4 checked the terminal factor `162·(2^−94 + 2^−30) < 1`.
4. **The theorem itself.** `manuscript_A7_actual` uses `Nat.strong_induction_on` over all n′, d′ and g. The degree-0 case is `manuscript_A7_degree_zero` (an equality). The positive case uses only `ih r hr`. There is no oracle and no aggregate premise.

**W2-2. The legacy degenerate A7 and A9 helpers are not on the final route. RESOLVED within the stated bounds.**
- The A11 text never refers to `a7_a9_preceding_output_sum_le`, `…graph_charge`, `a7_a9_zero_parent_family_le`, `a9_initial_datum_card` or `a9_fiber_triple`.
- The A9 route goes through `a9AmbientA8PartitionEquiv` (used inside `a11GlobalA9PartitionEquiv`) and `a9Ambient_fixed_fiber_coarse_charge` (used inside `a11_actual_fixed_final_saved_charge`).
- A11 does take `a7_global_parent_unique`, `a7_carrier_parent_spec` and `a7_positive_of_mixed_bound` from the legacy A7Transfer file. Packet 4 classed these as unconditional injections or explicitly conditional theorems, not the degenerate helpers.
- **Boundary:** this absence claim covers the A11 text plus the trace of the exact 172 roots and the four focused consumers. It does not cover the rest of the repository.

**W2-3. The unused `_horder` premise and the support window. RESOLVED.** This resolves packet 5 proof F2 and complexity N1 / questions 3–4.
- **Where `_horder` is discharged:** in the `ho : a6Order t ≤ D` branch of `a11_weighted_mixed_sum_le_actual_initial_sum`.
- **Orders above D:** they vanish by `a7_derivative_fourth_zero_of_high`; they are not dropped by assumption.
- **The A9 coarse-charge window:** each case is handled.
  - When `dim A + codim B + k ≤ D`, the coarse charge applies.
  - When it is greater than D, the energy is exactly 0 by `a11AmbientEnergy_zero_outside_window`.
  - Fibres with `i > dim A` or `j > codim B` are proved empty by finrank contradictions.

**W2-4. The A8 and A9 overlap and the cubic and exponent costs. RESOLVED.** This resolves packet 4 proof F2, the "overlap multiplicity" question.
- **Exact reindexing:** the global initial-data bijection `a11GlobalInitialEquiv` has both inverse laws, so (A,B,t) maps one-to-one to (C,H,X). Restricting to positive order is exactly the nonzero-pair condition (`a11_nonzero_iff_order_pos`). Splitting by grade (`a11GlobalA9SourceEquiv`) and the per-grade partition are exact.
- **Each cost is charged exactly once:**
  - the A8 factor `2^(6Dk)`;
  - the A9 fibre factor `2^(3D(i+j+k))`;
  - the degree drop `2^(100(D−t)²)`;
  - the A6 weight `2^(24Dt)`.
- **Rank agreement:** the A8 rank k (of the initial pullback) equals the A9 final rank k. The source sigma records the rank of X, and the target fixes Y with rank Y = k.
- **Arithmetic, checked by hand:**
  - A10: `100(D−t)² + 27Dt + 6Dk ≤ 100D² − 63Dt − 4Dk` reduces to `10t² + Dk ≤ 11Dt`, which holds because k ≤ t ≤ D.
  - Tail when k ≥ 1: `2·2^(−67Dk) ≤ 2^(−31D(k+1)−4Dk)` reduces to `1 + 31D ≤ 32Dk`, which holds for D ≥ 1.
  - Tail when k = 0: `4r ≤ 2^(−31D)` reduces to `2 ≤ 32D`.
  - The W6 step: `−35Dk ≤ −6Dk`.
  - The W6 enlargement sums over **all** (A,B), including (⊥,⊤), and over all Y, including rank 0. That matches `a7HybridQ`.

**W2-5. Documentation only: stale A11 docstrings. LOW, retained.** The "accepted with notes at frozen run 56" header and the "forthcoming actual A9 aggregate" docstring carry no weight in either direction. `backward.isDefEq.respectTransparency false` affects elaboration only.

**W2-6. Q is not bounded above. RETAINED, outside this window.** A7 only bounds the fourth moment by `2^(100D²)·Q`. The fact that makes Q useful (`a12_Q_le_influence_mass`, A12) lives in another window's files. This window makes no claim of a Q upper bound.

### DR6 (signed incidence and normalization)

**W2-7. F1 and F2 are disjoint. RESOLVED.** This resolves packet 5 proof and non-claims F9. `DR6F1Witness` leaves out the kernel-spanning condition, but the final assembly (`dr6_actual_complex_convolution_partition`) splits the fibre by `P` and `¬P` through `Fintype.sum_subtype_add_sum_subtype`. The ¬P side injects into F1 pairs through `dr6_matrix_f1_or_f2_coverage` (`dr6ComplementToF1Pair_injective`). Nothing relies on F1 and F2 being disjoint.

**W2-8. The signed incidence and its normalization are exact. RESOLVED.** This resolves packet 6 questions 1–3 (Convolution definitions, filter bridge, Möbius identity). Checked:
- **q-Pascal:** `dr6_actual_gaussian_recurrence` is the form `[n,k] = [n−1,k] + 2^(n−k)[n−1,k−1]`.
- **Alternating sum:** `w_{k+1}·2^(n−k) = −2^n·w_k` gives `S(n+1) = (1−2^n)S(n)`, so S(n) is the product ∏(1−2^i), and the i = 0 factor kills it for n ≥ 1. The indicator is `1 − S(n) = 1_{n>0}`.
- **Kernel side:** `dr6KernelSuperspacesEquiv` uses an actual dual-annihilator / coannihilator equivalence. It is not a Gaussian-count stand-in.
- **Grid:** the grid factors as I + K − IK, and zero-grade cardinalities equal 1.
- **The obstruction predicate:** `DR6F2Obstruction` is literally image-meet ≠ ⊥ or kernel-join ≠ ⊤ (`dr6_f2_actual_union_iff_manuscript_obstruction`).
- **The selector bridge:** `dr6_complexSelector_iff_actualOrdinary` proves the coordinate-annihilator selector equals `DR6OrdinarySelected`.
- **Shared index type:** A11 indexes with the same `dr6ActualNonzeroABPairs` type that Moment uses.

**W2-9. DR6 constants. RESOLVED arithmetically; manuscript fidelity RETAINED.**
- **F1:** `2^(rank X²) ≤ 2^(4D²)` (outer splits) times `(2^(D²)·E|f|²)²`. The global injection (X,(A,B)) → (A,B) is used exactly once.
- **F2:** `7D(i+j)` decomposes as Möbius `D` + carrier count `2D` + weighted Cauchy `4D`. The `(16/15)² − 1 = 31/225` bound needs D ≥ 1, and that is enforced. Grades above D are exactly zero. Outputs of rank above 2D are exactly zero.
- **The final step:** `(2a + (62/225)S)/162 ≤ a + S`.
- **What is open:** the formal proof uses Gram–Cauchy, not the docstring's Rademacher argument with its factor 81, so the constant 162 is valid but slack. Whether these constants match the manuscript cannot be checked without the manuscript text for lines 1385–1386 and 1513–1615.

**W2-10. Stale DR6 status text. LOW, retained.** The docstrings in Moment ("uncompiled, uncertified"), Incidence ("remain open"), Mobius and Convolution ("does not claim DR6", real-valued f, the Rademacher route) all predate the code. They carry no weight either way.

**W2-11. Hygiene. INFO.**
- A stray `end` sits before `dr6_f2_a5_global_fixed_D_ambient_bound`.
- Unused: `{D}` in `…remainder_eq_signedCoefficient`, `hKB`, and the real-valued `DR6OrdinaryFilter`.
- The grid-Cauchy lemma on `dr6F2NonzeroGradeGrid` is off the final route.

### A18, A20, A21 (influence → globalness → square → moment)

**W2-12. The A18 budget and absorption. RESOLVED.** This resolves packet 2 proof F1 / question 1 and complexity question 1.
- `a18BudgetScale D r eps = 2^(10Dr)·eps` (now visible in InductionBounds).
- **Top term:** `10(D−1)(r−1)+10 ≤ 10Dr` holds because D + r ≥ 2, and `2D+10D(r−1)+8 ≤ 10Dr` holds because D ≥ 1. Together they give 9/512.
- **Geometric step:** `Σ_{i<D} q^i ≤ q^D/31` holds for q ≥ 32.
- **Final combination:** `1/2 + 2/961 ≤ 1`. The top level `9/512 ≤ 1/4` gives the `K/2` share.
- **Induction hypotheses:** each is used at strictly smaller (D, r), with ε unchanged on the derivative branch. The cost-one derivative inherits influence D−1 by A1 composition plus exact cost addition (`relative_endpoint_cost_add`). The base cases D = 0 and r = 0 are separate. There is no conditional-fibre premise.

**W2-13. Whether order 0 belongs in `OriginalActualInfluenceThrough`. LOW, retained (packet 2 non-claims F1).** The definition includes A = ⊥, B = ⊤, which bounds the ambient energy. In this window's consumers the extra condition is discharged: A20 gets it from A16, which holds for every carrier, and packet 1 says A22 gets it from the zero-cost identity. It is a stronger premise only if A18 is cited on its own as the manuscript's theorem. Settling that needs the manuscript's definition of influence.

**W2-14. A16 is used with no cost condition. RESOLVED (packet 2 F2).** `a20_three_degree_global` never uses `_hcost`. That is consistent with packet 7's reading of `filteredCarrierFunction_energy_le_A16`: its only premises are support and up-to-D globalness, for any (A,B,T). The budgets check: `30D² + 11D² = 41D²`, then `114 + 41 + 41 = 196`.

**W2-15. A21 recurrence and scope. RESOLVED.**
- `a(2q) − 4a(q) = 200q ≥ 98q − 82`.
- ε powers: `1 + (q−2) = q − 1`.
- Base cases: p = 2, and p = 4 via A19 (114 ≤ 2800).
- The induction quantifies over every n, d, D, ε and f, so applying it to f² at degree 2D is legitimate.
- **Scope:** only natural dyadic p ≥ 2. That matches the scope correction that A22 is stated for natural dyadic p with real conjugate q. The A22 signature and `pConjugate` bodies are not in this window; this window confirms only the A21 side.

**W2-16. Dependency direction and the constants between A18, A21 and A22. CONSISTENT, direct check retained.**
- Lean imports are acyclic, so circularity is impossible at the module level, and inside A18 and A21 the induction is well-founded.
- The direction is A16 → A18 → A20 → A21 → A22 → HC46.
- Packet 1's A22 arithmetic, `200j²p² + 10j²(m−1) ≤ 810j²m²`, matches A21 applied at `eps = a18BudgetScale j j E = 2^(10j²)E`.
- What remains is to inspect the A22 body directly and confirm it makes exactly that instantiation. That belongs to another window.

### HIGH and Medium items this window's sources cannot settle (all RETAINED)

**H1 (packet 7, HIGH F1): does the universal `original_HC46_exact` instantiate `hHC` in the same material-moment consumer?**
- **What follows logically:** if the constant `original_HC46_exact` has type exactly the same fully qualified `HC46ExactContract` that `selected_actual_material_moment_bound` takes, then the term `selected_actual_material_moment_bound (hHC := original_HC46_exact) …` type-checks.
- **What it would still need:** that instantiation still requires `hSpectral : Spectral47ExactContract …`, which is open, plus `hfail`.
- **What is not there:** no hHC-free material export appears among the 172 roots. Only `selected_leaf_HC46_original` and `selected_leaf_failed_zoom_HC46_original` are roots.
- **Evidence still missing:** the stated type of `original_HC46_exact`, the definition of `HC46ExactContract` with its namespace, and the bodies of the two wrappers. These are OriginalExactInhabitant, SelectedComplementHC46OriginalApplication and AnalyticMoment, none of which is in this window.

**H2 (packet 7, HIGH F2): is the contract false, or vacuous?** **Partly narrowed, not closed.**
- **The "false" half:** a kernel-checked inhabitant with standard axioms would rule out `HC46ExactContract` being false, but only if its type is confirmed as in H1.
- **The "vacuous" half:** this still needs the `BinaryMatrixFourier` bodies: `PseudorandomExact`, `exactWholeRestriction`, `boolean_mean_le_of_exact`. It also needs the padding lemmas in `ActualBinaryMatrixHC46`. Those would establish the whole fibre at every r, ε ≥ 0, and the zero-density branch.

**M1: exact versus nominal budget.** Still open from packet 8 F1/F5, packet 9 F1/F2 and packet 7 F4. The items to check:
- zero-row padding;
- flag averaging at the exact actual budget;
- the guards `r < d` and `b < k`;
- the same pre-drawn T and f;
- the factor 2;
- the bodies of `exact_zoom_implies_nominal_pseudorandom`, `smaller_budget_of_exact_r` and `ActualLeafLabelRankImageAlignment`.

None of these is in this window. `PseudorandomExact` is still a **one-sided** upper bound on density.

**M2: typed A14/A15/A16 definitions and transports.** Not in this window. Packet 7 and packet 8 reports are reused unchanged.

**M3: the five historical draft-banner files.** Native evidence shows all five with pinned hashes and their imports inside the 319-file closure. So their membership in the closure is established. The banners themselves carry no weight. This was resolved from evidence, not reviewed in this window.

---

## What this window can safely claim

Under the qualified native evidence and the pinned library trust, the 10 pinned files in this window establish:
- **`manuscript_A7_actual`:** for every finite binary matrix space and every complex f supported through D, the fourth moment is at most `2^(100D²)·a7HybridQ f`. This is by simultaneous strict strong induction, with a genuine weighted `hS` built from actual A8, A9, A10 and W6. The legacy degenerate helpers are not used, within the bounds stated in W2-2.
- **`dr6_actual_complex_fourth_moment_over_162_le`:** for arbitrary complex f with Fourier support through D, with an exact F1/F2 partition and exact signed Möbius incidence.
- **`actual_A18_original_global`:** original influence implies actual globalness at `2^(10Dr)·ε`.
- **`manuscript_A20_actual`:** square globalness at `2^(196D²)·ε²` through order 2D.
- **`manuscript_A21_actual`:** the moment bound `2^(200D²p²)` for **natural dyadic** p ≥ 2.

**Not claimed by this window:**
- the HC46 contract, its inhabitant, the selected wrappers, and whether `hHC` is used in the material-moment consumer (H1, H2);
- Spectral47, or any material, reduction, runtime or learning acceptance;
- a useful numerical "no" bound;
- an upper bound on Q;
- that the manuscript's constants and definitions match (order 0 in influence, 162, 7D(i+j), 31/225);
- the A22 body and the real-q interface;
- zero total warnings;
- any absence claim across the whole repository;
- integration complete, or the full manuscript.

## Questions to carry into the other windows

1. The exact type of `original_HC46_exact`, and whether it is the same constant as `HC46ExactContract` in AnalyticMoment (H1).
2. Non-vacuity of `PseudorandomExact` at every r, ε ≥ 0, and the zero-density branch (H2).
3. The exact-budget and nominal-padding chain, with every guard (M1).
4. That the A22 body instantiates A18 at `r = level` and A21 at `eps = 2^(10j²)E`, with q = `pConjugate p` (W2-16).
5. The manuscript text for influence order 0 and for the DR6, A7 and A18 constants (W2-9, W2-13).
6. Spectral47 and the useful numerical bounds, both still open.
