# Proof-adversarial review of Full95: the four new bodies and their integration into the material theorem

## Verdicts

| Scope | Verdict |
|---|---|
| Native, conditional integration of the material statement: the old export, the new SourceSize export and the two new dyadic exports | **GO-WITH-NOTES, conditional on reconciling hash finding H-1.** I found no soundness, quantifier, direction or substitution defect in the four new bodies. |
| Overall integration GO | **Not issued.** H-1 is an unresolved HIGH identity finding. R14, a HIGH runtime finding from the earlier review, also remains open on the reduction gate. |
| Unconditional material readiness | **Incomplete.** Spectral47, a useful `e`/`a` (numeric NO), `U`/`copies` that can be inhabited together, and an instantiated scalar cutoff are all still open. |
| Manuscript | **No verdict.** Nothing here is accepted, and I make no claim about novelty, priority or publication. |

**How I reviewed.** I used no tools, wrote nothing, ran no Lean or Lake, and recomputed no hashes. The compile results, axiom profiles, trace and custody facts come from the receipts you supplied. I treated the three author notes as hypotheses, not as certificates.

## Coverage

**Inspected in full (67 supplied files, none skipped):**
- **4 new project files:**
  - `ActualSelectedComplementSourceSizeAppendMoment`
  - `ActualSelectedComplementSourceSizeAnalyticMoment`
  - `ActualSelectedComplementSourceSizeOriginalApplication`
  - `ActualSelectedComplementManuscriptDyadicMoment`
- **40 prior project files.** These are the 5 critical files (OriginalApplication, AnalyticMoment, AppendMoment, OriginalExactInhabitant, LeafLabelRankImageAlignment) and the 35 reached support modules from the earlier review. I re-read the ones the new bodies call against those calls.
- **23 Complexitylib files.**

**Not re-read:** the other 279 prior bodies are reused by identity only, under the reuse audit (`reuse_identity_eligible: true`, 7979 constant types and edges unchanged). Identity reuse is not a re-reading, and I don't claim one.

### New declarations reviewed

**SourceSizeAppendMoment**
- `selected_rankloss_exponent` (private)
- `rankloss_from_exponent` (private)
- `selected_actual_append_moment`
- `selected_actual_center_identity`

**SourceSizeAnalyticMoment** (namespace `…SourceSizeAnalyticMoment`)
- **Contracts and selectors:** `HC46ExactContract`, `Spectral47ExactContract`, `selectedF`, `selectedG`
- **Leaf and HC46 lemmas:** `selected_leaf_indicator_basis_invariant`, `selected_leaf_HC46_of_exact_PR`, `selected_leaf_failed_zoom_PR`
- **Level split:**
  - `selectedLevel`, `selectedLowIndexSet`, `selectedLow`, `selectedHigh`, `selectedHighFin`, `selectedHighFinIndexSet`
  - `selectedHighFin_eq_selectedHigh`, `selectedHighFin_eq_finset_sum`
  - `rankProjection_finite_reconstruction`, `selected_append_low_high_decomp`
- **Append-average and Lp moments:**
  - `appendAverage_finset_sum`, `appendAverage_abs_pow_le`, `appendAverage_lpMoment_le`
  - `lpMoment_le_pow_of_lpNorm_le`, `selected_leaf_append_level_HC46`
  - `selectedLowHC46NormBound`, `selected_low_append_HC46_lpNorm_bound`
- **Event moment and threshold bounds:**
  - `selectedActualMoment`, `pow_add_le_two_pow` (private), `appendAverage_indicator_mem_unit_interval`
  - `actual_append_threshold_pointwise`, `actual_append_threshold_mean_bound`, `actual_append_threshold_mean_bound_beta`
  - `exists_dyadic_exponent_for_actual_moment`, `selected_low_weighted_holder`, `selected_center_matrix_mean_le_exact_grassmann_beta`
  - `selected_actual_event_moment_bound`, `selected_actual_event_moment_holder_bound`, `selected_actual_reconstructed_holder_bound`, `selected_actual_moment_def`
- **High-level energy and spectral step:** `appendHighLevel_energy_eq_sum`, `appendHighLevel_energy_le_spectral_sum`, `selected_leaf_high_energy_le_spectral`
- **Exponent window and final assembly:**
  - `real_pow_moment_div_m_eq_pow`, `exists_dyadic_moment_exponent_window`
  - `selected_actual_HC_spectral_moment_bound`, `selected_actual_analytic_rhs`
  - `matching_center_mass_eq_grassmann_beta`, `selected_actual_source_dimension_bound`, `selected_actual_material_moment_bound`

**SourceSizeOriginalApplication**
- `selected_leaf_HC46_original`
- `selected_leaf_failed_zoom_HC46_original`
- `selected_actual_material_moment_bound_original`

**ManuscriptDyadicMoment**
- `selected_actual_HC_spectral_moment_bound_at_dyadic_exponent`
- `selected_actual_material_moment_bound_at_dyadic_exponent`
- `selected_actual_material_moment_bound_original_at_dyadic_exponent`

## Core checks, re-derived from the source

**1. The source row count is independent of `m`.**
- All three SourceSize theorems now take `I : Instance N rows`, where `rows` is a fresh implicit binder.
- I checked every use of `I` in the new bodies:
  - `TaggedGoodU I copies J`
  - `SideComplement I copies U`, with `sideComplement_finrank` equal to `2J`
  - the coordinate-transport tables and the functional
- None of these mentions `rows`.
- `m` now appears only as:
  - the selector output (`hsel`);
  - the leaf-query count (`matchingStarMass (m := m)`, i.e. the star arity is `m` leaves);
  - the moment power;
  - the parameter in `bOf m`, `leafT` and `leafK`.
- The old `Instance N m` theorems are the special case `rows := m`, and they remain among the 181 roots.

**2. Dimensions and rank loss.** The private lemmas match the reviewed AppendMoment versions token for token.
- They give `c+s = 2h` and `c + m·s + 2h ≤ 2h(m+2) ≤ 2h² < 2J`, using `m+2 ≤ h` and `A ≥ 1`.
- The rank loss is at most ½.
- `hsmall'` rewrites the finrank of `CoordinateAmbient (2J)` to `2J`.
- `selected_actual_source_dimension_bound` derives `c+s ≤ finrank A.1 = 2J` with no instance premise.
- `n = 2J` is the actual appended-matrix row dimension. The `hdim : c+s ≤ n` used by the HC/spectral bound is derived, not assumed.

**3. The caller's floor and cutoff in `analyticSourceHeightFloor`.**
- The material theorem uses `selected_spectral_parameters` at the exact `ρ = leafK/(2h) = 1/bOf m`. It gets `hcutFloor : cutoff ρ ≤ h` at that same `ρ`, and passes that same `sourceHeightCutoff` to Spectral47.
- `base` stays a free choice of the caller and is only carried along (`hbaseFloor` is unused).
- **Not yet done:** instantiating the floor with the quantitative inverse cutoffs from the scalar-calibration note.

**4. HC46: the original inhabitant and how it is applied.**
- `original_HC46_exact` is typed against `ActualSelectedComplementAnalyticMoment.HC46ExactContract`, the old constant.
- The new exports expect `…SourceSizeAnalyticMoment.HC46ExactContract`, a separate constant. Its body is the old one with the binder renamed from `hEven` to `_hEven`; the two are α-equivalent. The kernel accepted `exact … original_HC46_exact …` by unfolding both definitions.
- The application inside the proof changed from `hHC (hEven := rfl)` to positional `hHC rfl`. This is the Full94 binder repair, and its meaning is unchanged.
- HC46 is still applied through the universal contract, at `b = selectedF Tc fc` with `hEven := hsplit`. The selected-leaf wrapper is not used, and no surrogate leaf replaces the actual one.
- The A22/A18/A21 chain is reached through the inhabitant, and the trace lists the A22 and inhabitant roots.

**5. The dyadic exponent is now chosen by the caller.**
- The original `selected_actual_HC_spectral_moment_bound` took `hklt : k < 8m` but never used it. Removing it is sound.
- The new bound needs `hkm : 4m ≤ k`, `hm : 0 < m` and `hkDyadic`. From these it derives:
  - `4 ≤ k` (the `hp4` that HC46 needs);
  - `0 < k`;
  - `m ≤ k`, hence `p/m ≥ 1` for Hölder.
- The exponent identities `(m/k)·k = m` and `(B^k)^{m/k} = B^m` still hold.
- The material conclusion now holds at the given `k` directly; there is no `∃ k`.
- **Info:** `k` is an implicit binder that the caller fixes through `hkDyadic`. To pick it explicitly, call with `(k := …)`.

**6. The right-hand side and the order of averaging.**
- `selected_actual_analytic_rhs` is unchanged:
  - `2^m·β^{1−m/k}·(Σ_{i≤r} 2^{500i²k}(2e)^{(k−2)/k})^m + 2^m·a^m·β + a^{−2}·Σ_{i>r}(2^{−i(s−1)} + 3·2^{i−n})·E[(P_i 1_F)²]`
- The averaging order is unchanged:
  - one uniform base `M`;
  - the `m` leaf draws are independent appended-column averages sharing that same `M`, with no conditioning on rank;
  - Jensen and Minkowski are applied on unconditional carriers;
  - `β` is the exact Grassmann center fraction, derived via `α ≤ 1`.
- The star-mass bound uses Grassmann ≤ 2·matrix together with the derived `hsmall`.

**7. The same objects are used throughout.** These all apply to the same `I`/`copies`/`U`/`A`/`C`/`T`/`f`:
- `Tc = selectedCoordinateLeafTable I copies U A T` in `hfail`, in the PR premise and in the moment;
- `Cc`/`fc` in the center identity;
- the transported tables in the matching masses.

The input and star scope is not narrowed anywhere.

**8. Spectral47 is still a premise of every new export.** It is now a separate constant per namespace, with an identical body.

## Findings

| ID | Severity | Declarations | Finding | What to do |
|---|---|---|---|---|
| **H-1** | **HIGH (identity, blocks overall GO)** | All 4 new files | The SHA256 in each supplied body's header does not match the receipt's `added_object_hashes` for the same path:<br>• AppendMoment: D4B86B56 vs 6E8EA03C<br>• AnalyticMoment: 03FB0A5D vs B472BC2E<br>• OriginalApplication: 22DE415F vs 3268034A<br>• Dyadic: AF3E380A vs C02909B6<br>Possible explanations are a different kind of artifact (cache object vs source), CRLF/LF normalization, or a version other than the one compiled. I can't tell which without tools. Until reconciled, this review is not bound to the bytes that were compiled natively. | Provide a pinned mapping from source SHA to object SHA, or recompute the source SHAs from the custody tarball. |
| N-1 | Resolved (was HIGH I3 / Medium R5) | `…SourceSize…material_moment_bound(_original)` | The row-count coupling is gone. For a fixed source `I`, `selector_unbounded` gives some admissible `m` for every large enough `L`, and the theorem applies at that `m`. It no longer needs the selector to land on a prescribed `m`. | Still needed: an effective `L₀`, and a joint witness for `U`/`copies` (`TaggedGoodU` needs about `J` rows, which is doubly exponential). |
| N-2 | Low | `HC46ExactContract` / `Spectral47ExactContract`, duplicated across namespaces | The two parallel constants are bridged only implicitly by definitional equality. A future Spectral47 proof aimed at one namespace still needs that bridge. | Add explicit `Iff.rfl` bridge lemmas between the old and new contracts. |
| N-3 | Verified | Dyadic exports | Dropping `k < 8m` is sound, and every guard that is still needed is derived. | — |
| N-4 | Low (stale text) | SourceSizeOriginalApplication block comment; Dyadic header ("Uncompiled candidate") | Contradicts the native receipt. Gives no weight either way. | Clean up before render. |
| N-5 | Info | Tactic-level edits: `let` replaces `letI`, smaller `simp` sets, unused `_hC`, `_hsum` and `_hbudget` binders | These affect elaboration only; the kernel checked the result. The anonymous `let : Nonempty …` acts as a local instance, and it compiled. | — |
| N-6 | Medium (open) | Spectral47 | Unchanged. The orbit-gain note is bounded Python evidence over 220 cases. The candidate same-range orbit helper is outside this capture and is uncompiled. The contract never uses `ρ`, `hHeight` or `hEven`, so its fidelity to manuscript 4.7 is still a question. | Machine proof for the actual append operator, plus a fidelity audit. |
| N-7 | Medium (open) | `selected_actual_analytic_rhs`, `hfail` | Numeric NO is still open. The scalar-calibration note gives sufficient finite-sum and scalar conditions only: author arithmetic, with only 3 examples where `m ≥ 256`. Taking `e = 1` makes `hfail` trivial. | Certified scalar consumer, a useful `e`, and control of `B`. |
| N-8 | Info | Trace | The native report has `consumption_trace_complete: false` and `source_selection_complete: false`. The structural trace does qualify: 8069 nodes, 0 unresolved. | Record the actual consumption trace. |

## Reconciling the earlier reports

**Fifteen packet reports**
- Export fidelity (PA1‑01/03, R1) carries over to the SourceSize exports; the old export is still a root.
- `hsmall`/`hdV` (C3, P5‑6) remain derived in the SourceSize copies.
- The untagged-vacuity claim (cx‑03 C1) remains a non-claim and is not reached.
- Results not on the trace (P3‑1, PA4‑01) are unchanged.
- Complexitylib (CX‑01…05, X1–X5, N3–N7) is unchanged: `algFamily` is reached only as carrier data. It is noncomputable, has no runtime theorem, and its gaps are existential.
- Stale banners (P5‑3, PA4‑03) remain, and two new ones are added (N-4).

**Three whole-integration reports**
- I3/R5 is resolved by N-1.
- Spectral47 (I4/R3), numeric NO (I11/R10) and the runtime HIGH R14 remain open.
- The selector effectivity part of I5/R4 is reduced to finding an effective `L₀`.
- Upstream selected profiles still provide no CMMSA bridge.
- The inherited warning debt is unchanged: zero owned warnings is not zero total warnings, and linter suppression remains.

## Safe conditional claim

This holds only once H-1 is reconciled, and rests on pinned kernel, Init, Mathlib and Batteries trust plus the native receipts (181 standard profiles).

For any `I : Instance N rows` with `rows` arbitrary, any `copies`, `U`, `A`, `C`, `T`, `f`, `base` and `cutoff`, suppose:
- `selector(…) L = m`;
- `1 ≤ samplerA`;
- `r < c+s`;
- `0 ≤ e`;
- `hfail(e)` holds on the same coordinate leaf table;
- `Spectral47ExactContract cutoff` holds;
- `a > 0`.

Then, with no HC46 premise:
- for the fixed window, there is a dyadic `k` with `4m ≤ k < 8m`;
- for every caller-chosen dyadic `k ≥ 4m`, `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)` and the matching center mass equals the exact Grassmann fraction.

**Not claimed:**
- Spectral47
- numeric NO, or a useful `e`
- selection before the draw, the table, or source arity beyond the binder generalization
- the sampler, robust8S, or source/star acceptance
- encoded runtime, reduction or learning
- expander explicitness
- upstream bridges
- zero total warnings
- publication

## Remaining to-do

1. **H-1:** reconcile the source SHAs of the four new files with the receipt's `added_object_hashes`.
2. Prove Spectral47 in Lean for the actual append operator: GL orbit, Fourier covariance, orbit counts, Parseval. Add `Iff.rfl` bridges between the duplicated contracts (N-2), and audit fidelity to manuscript 4.7.
3. Certify the scalar consumer: choose `r`, `T` and dyadic `P ≥ mT`, prove the finite-sum and scalar comparisons, instantiate `base`/`cutoff` in `analyticSourceHeightFloor`, and give an effective `L₀`.
4. Prove `hfail` with a useful `e` on NO instances, and bound the high energies `B`.
5. Build a joint inhabitance witness for `I`, `copies` (`TaggedGoodU` at `J`), `U` and `A`.
6. Complete source/star: acceptance → a fixed `f` on the trace, `AllAmbientInverse`/robust8S, and discharging `kappa`/`hexpand`.
7. Encoded reduction and runtime (R14: `J` is doubly exponential), an explicit expander, and learning.
8. Post-audit of the upstream selected profiles, then the CMMSA bridges.
9. Dispose of warnings and logs, remove stale banners (N-4 included), and replay from a fresh checkout.
10. Manuscript fidelity, novelty, citation and BibTeX QA, PDF render, and the final full-scope providers.
