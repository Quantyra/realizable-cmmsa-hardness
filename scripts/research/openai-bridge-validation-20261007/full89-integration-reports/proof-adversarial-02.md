# Full89 integration, window 2/3 (analytic induction and incidence): independent proof-adversarial review

## Verdict

**This window: GO-WITH-NOTES.** It covers only the ten complete bodies supplied here and the cross-partition contracts they carry.

**Overall integration: INCOMPLETE.** Two HIGH items (H-1 and H-2) can't be closed from this window's sources. Several Medium items are also kept open for other windows or for the manuscript.

I used no tools, ran no Lean or Lake, and wrote nothing. I cite declarations by name rather than line number, because I can't count lines reliably without tools. The native stdout, the qualified audit, the 319 source pins and the 566-object identity are taken as qualified receipts. Kernel acceptance of these bodies rests on them.

## Body coverage (10 supplied, 10 inspected in full, 0 skipped)

| File | SHA256 (supplied) | Status |
|---|---|---|
| ActualBinaryMatrixHC46A11WeightedAggregate | B296A5A9… | inspected |
| ActualBinaryMatrixHC46DR6Convolution | CDDF6433… | inspected |
| ActualBinaryMatrixHC46DR6Incidence | 31305E6B… | inspected |
| ActualBinaryMatrixHC46DR6Mobius | 6E2CCA4E… | inspected |
| ActualBinaryMatrixHC46DR6Moment | 500BF0B2… | inspected |
| ActualBinaryMatrixHC46DR6SignMoments | DAFA4306… | inspected |
| ActualBinaryMatrixHC46A18OriginalGlobalInduction | C4513E43… | inspected |
| ActualBinaryMatrixHC46A18InductionBounds | D583B3DA… | inspected |
| ActualBinaryMatrixHC46A20SquareGlobalness | 435873CF… | inspected |
| ActualBinaryMatrixHC46A21DyadicMoment | 2B3FE7D9… | inspected |

Some bodies needed for the HIGH questions are not in this window, so I did not skip them, but they are absent here:
- A22 (OriginalInduction, ParentFactorization, OperatorLq)
- RealQNorm and RealQTransport
- OriginalExactInhabitant
- SelectedComplementAnalyticMoment and AppendMoment
- BinaryMatrixFourier and ActualBinaryMatrixHC46
- the MatrixLift files

## Native evidence, as read
- **Profiles:** all printed root profiles are subsets of {propext, Classical.choice, Quot.sound}. `a21_exponent_le` is [propext] and `a21_density_recurrence` is [propext, Quot.sound]; both are harmless subsets.
- **DR6, A9 and A7-consumer declarations are not requested roots.** Their axiom cleanliness comes transitively, because `#print axioms` is transitive, and only for constants inside some root's closure. The DR6, A9Ambient and A7 files are pinned `transitively_consumed: true`.
- **New observation (see N-3):** the pin for `ActualSelectedComplementAppendMoment.lean` reads `transitively_consumed: false`. None of the 172 roots or the four focused consumers reaches any of its constants. The material-moment route therefore has no native axiom profile in fresh172.

## What this window resolves, independently checked

**1. A11 discharges the genuine hS with a strict lower-degree hypothesis. Resolved within the window.**
- **Induction structure:** `manuscript_A7_actual` uses `Nat.strong_induction_on` over `e`. It is simultaneous over all `n' d' g`. The base case `e=0` comes from `manuscript_A7_degree_zero`. For `e>0` it builds `a11StrictLowerDegreeIH e` from `ih r hr`, so only strictly smaller degrees are used. There is no oracle and nothing circular.
- **Where the IH is used:** only in `a11_actual_mixed_fourth_le_output_q`, at degree `D − order`. `D − order < D` follows from `hpos` by omega.
- **Assembly of hS (`a11_original_weighted_mixed_bound`), in order:**
  1. Per-triple bound. When `order > D`, the term is exactly zero by `a7_derivative_fourth_zero_of_high`; it is not dropped by fiat.
  2. Bijective reindex to positive initial data (`a11NonzeroInitialEquiv`). The order equality holds by `rfl`.
  3. Exact A9 partition (`a11GlobalA9SourceEquiv` followed by `a9AmbientA8PartitionEquiv` per grade).
  4. Fixed-final saved charge.
  5. Finite i/j tail.
  6. W6 terminal bound ≤ 2Q.
- **Exponents, re-derived by hand:**
  - A10 saving reduces to `100t² + 10Dk ≤ 110Dt`, using `t ≤ D` and `k ≤ t`. ✓
  - `24Dt + 3Dt + 6Dk` plus `100(D−t)²` fits under `100D² − 63Dt − 4Dk`. ✓
  - Tail, `k>0`: needs `1 + 31D ≤ 32Dk`. ✓
  - Tail, `k=0`: `4r ≤ 2^(2−63D) ≤ 2^(−31D)`. ✓
  - W6 denominator: `−31D(k+1) − 4Dk ≤ −31D − 6Dk`. ✓
  - Total: `2^(100D²)·2^(1−31D)·Q`. This matches the hS shape that `a7_positive_of_mixed_bound` consumes, and the native compile confirms the types match.

**2. Actual A9 fibre and partition, support-window split, `_horder`. Resolved.** This answers packet-5 Q3 and complexity N1.
- **`_horder`:** supplied from the `ho : a6Order t ≤ D` branch when A11 calls `a8_output_q_le_actual_predecessor_sum`.
- **Case split in `a11_actual_fixed_final_saved_charge`:** it is exhaustive.
  - If `i > dim A`, the fibre is empty: the dimension contradiction comes from `A0`.
  - If `j > codim B`, the fibre is empty: the contradiction comes from `B ≤ B0` and the quotient dimensions.
  - If `dim A + codim B + k > D`, the energy is zero by `a8_actual_energy_zero_outside_supported_window`, through `a11AmbientEnergy_zero_outside_window`.
  - Otherwise `a9Ambient_fixed_fiber_coarse_charge` applies.
- **Which A9 constants A11 uses:** in its text, A11 calls only `a9AmbientA8PartitionEquiv` and `a9Ambient_fixed_fiber_coarse_charge`. It does not call `a9_initial_datum_card`, `a9_fiber_triple` or any `a7_a9_preceding_*` helper. This is a textual check of this file only.

**3. A8 overlap and cubic cost (packet-4 Medium F2). Resolved at the consumption level.**
- Every output pair is charged once through the A8 bijections in the endpoint. The multiplicity of final pairs over initial data is paid exactly once, by the A9 fibre count `2^(3D(i+j+k))`.
- The A8 graph/cube factor `2^(6D·rank)` appears once. It sits on the left of `hc` and is retained on the right, never doubled.
- This rests on the endpoint and coarse-charge statements, which packet 5 reviewed in full.

**4. DR6 signed incidence and normalization. Resolved.** This also answers packet-5 F9 and packet-6 Q1–Q3.
- **Selector bridge:** `DR6ComplexOrdinarySelected` ⇔ `DR6OrdinarySelected` via `dr6_kernel_le_iff_annihilator_le_range`. The underlying identity is range Y = coordinate annihilator of ker Yᵀ, obtained from `range_dualMap_eq_dualAnnihilator_ker` with dual-coordinate transpose (`dr6_dualMap_coordinates`). This is actual duality, not a count proxy.
- **Möbius identity:** the q-Pascal recurrence `G(n+1,k+1) = G(n,k+1) + 2^(n−k)G(n,k)` is proved from the actual W6Grass counts. It gives Σ G·(−1)^k 2^(k(k−1)/2) = ∏(1−2^i), which is the indicator 1_{n>0}. The signed grid factorization gives I + K − IK exactly. Absolute values enter only after `..._eq_original_obstruction_sum`.
- **Constants:**
  - α_k² ≤ 2^(Dk) needs k−1 ≤ D.
  - Carrier count ≤ 2^(rank X·(i+j)) ≤ 2^(2D(i+j)).
  - Weighted Cauchy gives 4D, for 7D in total.
  - The nonzero-grid factor is (16/15)² − 1 = 31/225 for D ≥ 1.
  - Grades above D vanish exactly.
  - Parseval normalization: Σ_X |coef of (Pf)²|² = E|Pf|⁴.
- **F1/F2 partition:** packet-5 F9 worried that F1 and F2 overlap. `DR6Moment` partitions each fibre by the F2 predicate and its complement, and injects the complement into the F1 pairs (`dr6ComplementToF1Pair`), so no disjointness is needed.
- **F1 route actually formalized:** this is a Gram–Cauchy argument, not the docstring's Rademacher/81 argument.
  - The per-X outer count is 2^(4D²).
  - The global (X,A,B) → (A,B) map is an injection.
  - The Frobenius bound is ≤ mass².
  - mass ≤ 2^(D²)‖f‖².
  - The formal F1 constant is therefore 1, so the stated 1/162 is valid with slack. This is a manuscript-fidelity note, not a defect (N-5).

**5. A18 constants. Resolved (packet-2 F1/Q1).**
- `a18BudgetScale D r eps = 2^(10Dr)·eps` is now read directly from the definition.
- `a18_top_contribution_le_nine512` is verified: it needs `10d0r0 + 10 ≤ 10(d0+1)(r0+1)` and `2D + 8 ≤ 10D`.
- `a18_lower_absorption` is verified: the geometric sum is ≤ 2^(5Dr)/31, and 1/2 + 2/961 ≤ 1.
- **Induction direction:**
  - The top layer uses `ihr (r−1)` and, for cost-one derivatives, `ihD (D−1)`.
  - The order-one derivative influence comes from `original_influence_order_one_derivativeCoordinate_reduction`. That is full-carrier A1 reindexing with exact additive cost (`relative_endpoint_cost_add`).
  - Lower layers use `ihD i`.
  - The non-exact branch uses monotonicity.
  - `eps ≥ 0` is derived, not assumed.

**6. A20. Resolved.** This answers packet-2 F2.
- At the call site in `a20_three_degree_global`, `filteredCarrierFunction_energy_le_A16 A B T f hsupport hglobal` takes no cost argument, so the A16 bound is cost-free. `_hcost` is genuinely unused.
- Exponent arithmetic: 30D² + 11D² = 41D², and 114 + 41 + 41 = 196.

**7. A21. Resolved.**
- The recurrence a(2q) − 4a(q) = 200q ≥ 98q − 82 holds.
- The eps exponent works out to 1 + 2(q/2 − 1) = q − 1.
- The base case at p=4 uses A19, with 2800 ≥ 114.
- The induction quantifies over all n, d, D and eps.
- The scope is natural p, `2 ≤ p`, `∃k, p = 2^k`. That is consistent with Root's correction that A22 does not quantify over arbitrary real p.

**8. A18/A21/A22 dependency direction and constants.** Confirmed as far as this window can go. Packet 1 quotes A22 using a parameter `2^(10j²)E`; this equals `a18BudgetScale j j E` from the definition here. The A21 envelope `2^(200D²p²)·E·eps^(p/2−1)` matches packet 1's `200j²p² + 10j²(m−1) ≤ 420j²p·m`. Whether `manuscript_A22_actual` actually takes q = `pConjugate p` has to be confirmed in the window that holds its body.

## Findings and dispositions

| ID | Sev. | Declaration / evidence | Disposition |
|---|---|---|---|
| H-1 | **HIGH (retained, narrowed)** | Universal `original_HC46_exact` instantiating `hHC` in `selected_actual_material_moment_bound` | Probably available at the type level, but not exported or evidenced. Packet 1 shows `selected_leaf_HC46_original` passing `original_HC46_exact` as the `hHC` argument of `selected_leaf_HC46_of_exact_PR`. Packet 7 shows that argument has type `HC46ExactContract`, an unparameterized universal Prop. Native success therefore implies the inhabitant's type is definitionally equal to the full contract, which would let it instantiate `hHC` in the same material consumer. **However:** (a) neither body is in this window; (b) there is no dedicated hHC-free material theorem among the 172 roots; (c) the material bound still needs `hSpectral` (Spectral47 is open) and `hfail`; (d) see N-3. Do not claim material-moment, reduction, runtime or learning acceptance. |
| H-2 | **HIGH (retained, narrowed)** | `PseudorandomExact` / `HC46ExactContract` vacuity (packet-7 F2) | If H-1's type identity holds, the contract is a theorem with standard axioms, so it cannot be refutable (modulo the consistency of Lean with those axioms). The "refutable contract makes consumers vacuous" scenario is then ruled out. What remains open is whether the *premise* is satisfiable and one-sided. That depends on `exactWholeRestriction`, padding, `boolean_mean_le_of_exact` and the zero-density branch, which are in BinaryMatrixFourier and ActualBinaryMatrixHC46 and not in this window. PseudorandomExact stays a one-sided upper bound. |
| N-1 | Medium (retained, manuscript) | `OriginalActualInfluenceThrough` includes order 0 (`original_influence_order_zero_seed`) | The chain is sound: every producer (A16 in A20, and A22) discharges order 0, so the premise is not vacuous. Whether the manuscript's influence definition also includes order 0 is still an open fidelity check. |
| N-2 | Medium → resolved | Packet-4 F2, packet-5 Q2/Q3, complexity N1/N3 | Resolved by §§2–3 above. |
| N-3 | Medium (new) | Pin: `ActualSelectedComplementAppendMoment.lean` has `transitively_consumed: false` | No root or focused consumer reaches the append-moment constants (`selected_actual_append_moment`, the rank-loss factor 2). So the material-moment theorem and any hHC-instantiated version of it have no fresh172 axiom profile. Compile membership in the 319 closure is the only native evidence. |
| N-4 | Low (retained) | A9InitialGraph and A7Transfer are `transitively_consumed: true` | The trace disposition shows only the named legacy declarations (`a9_initial_datum_card`, `a9_fiber_triple`, `a7_a9_*`) absent. It does not list which of these files' constants *are* reached. The A11 text doesn't need any of them, but to bound route-crediting completely, enumerate the reached constants. |
| N-5 | Low (manuscript) | DR6Convolution docstring (Rademacher/81 route) vs the formal Gram–Cauchy F1 | The formal result is stronger (factor 2 instead of 162). Any manuscript proof description must match whichever route is cited. |
| N-6 | Low | Stale comments: DR6Moment ("uncompiled and uncertified"), DR6Incidence ("global… remain open"), DR6Mobius header, A11 ("forthcoming", "accepted… frozen run 56"), A20 ("candidate") | No evidentiary weight in either direction. Native GREEN covers compilation; review acceptance is not implied. |
| N-7 | Info | `dr6_actual_complex_f2_remainder_eq_signedCoefficient` has an unused `{D}`; DR6Incidence's final theorem sits after `end`; private `fibreEnergy_const_of_nonempty` is unused; `respectTransparency false` is set in A11 and A20 | Elaboration-only or hygiene. The kernel re-checks everything. |
| N-8 | Info → resolved | Root disposition: natural dyadic p with real conjugate q | Confirmed from A21. Confirming the A22 signature and RealQ Hölder belongs to the A22 window. |

## Cross-window questions still open (needed to close integration)
1. **Exact text:** the definitions of `HC46ExactContract`, `original_HC46_exact` (its declared type) and `selected_actual_material_moment_bound`, read together. This would confirm H-1's type identity and that `Tc`/`fc`/`r`/`e` are the same predrawn T/f.
2. **Pseudorandomness and zoom definitions:** `PseudorandomExact`, `exactWholeRestriction`, padding, the zero-density branch, `exact_zoom_implies_nominal_pseudorandom` (strict guard r<d, flag averaging at the actual exact budget, factor 2) and `ActualLeafLabelRankImageAlignment` (H-2).
3. **A22 body:** `manuscript_A22_actual` taking q = `pConjugate p` with dyadic natural p, and its use of `actual_A18_original_global` at r = j.
4. **A16 transports:** the typed A14/A15/A16 transports consumed by A22's parent factorization. A18's line and hyperplane A1 means are present here; their consumers are not.
5. **Missing statements:** an enumeration of the reached constants in A9InitialGraph and A7Transfer (N-4), and a native profile of an hHC-free material theorem if one is ever claimed (N-3).
6. **Manuscript:** order-0 influence (N-1), the DR6 constants 162 / 6D² / 7D(i+j) / 31/225, and the proof-route text (N-5).

## Safe claim boundary for this window
**Can be claimed,** conditional on the qualified native receipts and on the external lemmas that packets 1–9 reviewed in full:
- `manuscript_A7_actual` holds for every degree, by a genuine strict simultaneous induction, with the actual A8/A9 accounting.
- The complex DR6 inequality holds with the unrestricted nonzero-(A,B) right-hand side and no extra premise.
- `actual_A18_original_global` holds from support plus full-carrier influence only.
- A20 holds at `2^(196D²)eps²`.
- A21 holds for natural dyadic p ≥ 2.
- All the constants that link these steps match.

**Cannot be claimed from this window:**
- the A22 real-q statement;
- hHC instantiation or acceptance of the material-moment consumer;
- PseudorandomExact semantics beyond a one-sided upper bound;
- Spectral47 or useful numerical NO bounds;
- source/star/robust8S, encoded reduction, runtime or learning;
- upstream builds, a fresh checkout or the final provider;
- manuscript, render or novelty fidelity;
- zero *total* warnings (inherited baseline debt is still open);
- any new review of Init, Mathlib or Batteries bodies, which stay trusted as pinned.

I give no full-manuscript verdict.
