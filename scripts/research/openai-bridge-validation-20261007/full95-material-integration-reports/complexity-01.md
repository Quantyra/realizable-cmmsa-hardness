# Full95 complexity review: four new bodies and the whole material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **Overall** | **NO-GO (held).** One HIGH finding is open (H1 below): the bytes I reviewed are not shown to be the bytes that were natively verified. |
| **Mathematics of the 44 project and 23 Complexitylib bodies supplied** | **GO-WITH-NOTES.** I found no soundness, quantifier or direction defect. The new SourceSize roots remove the row-count coupling that blocked Full90. |
| **Native and material conditional integration** | Correct as conditional statements, but **this depends on H1**. A native GREEN result is not semantic or publication acceptance. |
| **Unconditional material readiness** | **NO.** Spectral47 is still a premise. There is no useful `e` or numeric NO result, and no joint witness for `I`, `copies`, `U` and `A`. |
| **Manuscript readiness, novelty, priority** | **Not assessed.** I give no acceptance of any kind. |

**How I reviewed.** I used no tools, writes, Lean, Lake or subagents, and I recomputed no hashes. Native, trace and custody facts come from the receipts you supplied. The scalar-calibration, spectral-orbit and citation notes are treated as author evidence. I re-derived what I could by hand and label those parts as uncertified.

## 1. Bodies inspected and skipped

All **67 supplied bodies were read in full; none were skipped.**

- **The 4 new files:**
  - `ActualSelectedComplementSourceSizeAppendMoment`
  - `ActualSelectedComplementSourceSizeAnalyticMoment`
  - `ActualSelectedComplementSourceSizeOriginalApplication`
  - `ActualSelectedComplementManuscriptDyadicMoment`
- **5 critical prior files, re-read:** OriginalApplication, AnalyticMoment, AppendMoment, OriginalExactInhabitant, LeafLabelRankImageAlignment.
- **35 other prior project files:** AppendFourier, SamplingBounds, both Cmmsa files, CoordinateMassBridge, EqualityCloud, Finite3Lin, FiniteLaw, FiniteMomentLp, AppendOperator, BinaryMatrixMoment, GraphEdges, OccurrenceAllocation, both OrdinaryStar files, RankImageInvariance, RhsFunctional, SelectedSpectralParameters, FixedRhoDimensionGuard, QuestionSupport, SpanIntersection, TaggedComplementIncidence, the density bridge, TaggedConcreteStarLaw, FixedCenterGeometry, FixedTableAcceptance, OrderedSampleNonempty, CoveringSpan, CoveringTV, EqualityGadget, FixedPortCycleFamily, MatrixGrassmannIdentity, PortCycleReplacement, SamplerParameters, TaggedFinite3Lin.
- **All 23 Complexitylib files.**

**Not re-read, and covered only by identity reuse.** These are reached modules whose bodies were not supplied. I make no claim to have re-read them:
- ActualSourceStarLaw, ActualFixedFunctionalStarMoment and ActualFixedFunctionalMatrixLift;
- the MatrixLift*, MatrixGrassmann{Fibre, Incidence, Moment, IntersectingAnchor} and GrassmannCounting/FlagPosterior modules;
- ActualMaximalPairLadder and ActualChangedAmbient8SBoundary;
- the whole HC46 A6–A22 chain, the TypedAB* modules and the BinaryMatrix A1/A14/A15 modules.

## 2. Complete new declarations

**SourceSizeAppendMoment:**
- `selected_rankloss_exponent` and `rankloss_from_exponent` (both private);
- `selected_actual_append_moment`;
- `selected_actual_center_identity`.

**SourceSizeAnalyticMoment** (a full parallel copy in a new namespace):
- Contracts and selected functions: `HC46ExactContract`, `Spectral47ExactContract`, `selectedF`, `selectedG`, `selected_leaf_indicator_basis_invariant`, `selected_leaf_HC46_of_exact_PR`, `selected_leaf_failed_zoom_PR`.
- Level splitting: `selectedLevel`, `selectedLowIndexSet`, `selectedLow`, `selectedHigh`, `selectedHighFin`, `selectedHighFin_eq_selectedHigh`, `selectedHighFinIndexSet`, `selectedHighFin_eq_finset_sum`, `rankProjection_finite_reconstruction`, `selected_append_low_high_decomp`.
- Append averages and moments: `appendAverage_finset_sum`, `appendAverage_abs_pow_le`, `appendAverage_lpMoment_le`, `lpMoment_le_pow_of_lpNorm_le`, `selected_leaf_append_level_HC46`, `selectedLowHC46NormBound`, `selected_low_append_HC46_lpNorm_bound`, `selectedActualMoment`, `pow_add_le_two_pow` (private), `appendAverage_indicator_mem_unit_interval`.
- Threshold, Hölder and event bounds: `actual_append_threshold_pointwise`, `actual_append_threshold_mean_bound`, `exists_dyadic_exponent_for_actual_moment`, `actual_append_threshold_mean_bound_beta`, `selected_low_weighted_holder`, `selected_center_matrix_mean_le_exact_grassmann_beta`, `selected_actual_event_moment_bound`, `selected_actual_event_moment_holder_bound`, `selected_actual_reconstructed_holder_bound`, `selected_actual_moment_def`.
- High-level energy: `appendHighLevel_energy_eq_sum`, `appendHighLevel_energy_le_spectral_sum`, `selected_leaf_high_energy_le_spectral`.
- Exponent and final assembly: `real_pow_moment_div_m_eq_pow`, `exists_dyadic_moment_exponent_window`, `selected_actual_HC_spectral_moment_bound`, `selected_actual_analytic_rhs`, `matching_center_mass_eq_grassmann_beta`, `selected_actual_source_dimension_bound`, `selected_actual_material_moment_bound`.

**SourceSizeOriginalApplication:**
- `selected_leaf_HC46_original`;
- `selected_leaf_failed_zoom_HC46_original`;
- `selected_actual_material_moment_bound_original`.

**ManuscriptDyadicMoment:**
- `selected_actual_HC_spectral_moment_bound_at_dyadic_exponent`;
- `selected_actual_material_moment_bound_at_dyadic_exponent`;
- `selected_actual_material_moment_bound_original_at_dyadic_exponent`.

### What changed from the prior bodies (diffed by hand)

- **Row count decoupled.** `Instance N m` became `Instance N rows` in `selected_actual_append_moment`, `selected_actual_center_identity`, `selected_actual_source_dimension_bound`, both material theorems and the export. The star arity, the selector output and the moment base stay `m`.
- **Binder-call repair.** `hHC (hEven := rfl)` became `hHC rfl`, and the contract binders became `_hEven`, `_basisInv` and so on. These are alpha-equivalent `∀` binders, so neither contract's meaning changes.
- **Tactic-only edits:** `simp [hrank]` became `simp`; `<;> ring` and `<;> omega` were dropped; `letI` became `let`; simp lemma lists were trimmed. Kernel acceptance of these rests on the receipt.
- **Dyadic module.** It is a verbatim copy of the HC/spectral moment proof with the `hklt : k < 8*m` binder deleted. I checked the prior proof: `hklt` was never used there; only `hkm` (through `hkm' : m ≤ k` and `0 < k`) was. Removing the ceiling is therefore sound. The conclusion now uses the caller's `k` directly, with no existential.

## 3. Checks requested in the brief

1. **Same objects throughout.** Every new root uses the same I, copies, U, A, C, T and f. The same `Cc`, `Tc` and `fc` appear in `hfail`, in the PR premise and in the moment, and the same `Cc` and `fc` in the center identity. The tables come from the same `selectedCoordinate*Table` and `coordinateFunctional`. There is no selected-leaf surrogate, and the input and star scope are not narrowed.
2. **`m` counts leaves and is independent of the source row count.** Confirmed for the SourceSize and Dyadic roots: `matchingStarMass (m := m)` and the arity `k := m` inside `hsmall` are tied to the selector output only, and `rows` is free. The old roots in `ActualSelectedComplement{Analytic,HC46Original}*` still carry `Instance N m`. Both exist and share bare names, so **citations must use fully qualified names.**
3. **SourceSize dimensions.** `c = leafT = 2(h − h/bOf m)` and `s = leafK = 2h − c = 2(h/bOf m)` (given `bOf m ∣ h`), `n = 2J`, and `c + s = 2h ≤ 2J`.
   - `hdim`, `hD` and `hsmall` are derived inline, and `c + m·s + 2h ≤ 2h(m+2) ≤ 2h² < 2J`.
   - `rankloss_from_exponent` bounds the loss by ½.
   - The strict-rank guard `hrd : r < c + s` is retained.
4. **`analyticSourceHeightFloor`.** The floor is `max(base m, cutoff(1/bOf m))`, wrapped as `max(·, j+2)`.
   - `selected_spectral_parameters` gives `cutoff(actualSelectedRho) ≤ h` at exactly ρ = 1/bOf m, and that is what `hHeight` consumes.
   - `base` and `cutoff` remain caller-chosen. Nothing instantiates them with the scalar note's quantitative cutoffs.
5. **The original HC46 inhabitant and its named application.** `original_HC46_exact` has the old-namespace type `ActualSelectedComplementAnalyticMoment.HC46ExactContract`. It is passed into slots typed with the new namespace's `HC46ExactContract`. The two definitions are textually identical up to binder names, so the kernel accepts the pass by delta-defeq. This is a genuine consumption of the A22/A18/A21 chain, not a surrogate. The same holds for `selected_leaf_HC46_original` and the Dyadic `_original` export.
6. **Caller-chosen dyadic exponent.** The theorem requires `hkDyadic` and `4m ≤ k`, with no upper bound.
   - This matches the scalar note: P is the least dyadic ≥ m·T with T ≥ 4, which can far exceed 8m.
   - For β ≤ 1 and k ≥ m·T, `β^(1−m/k) ≤ β^(1−1/T)` holds.
7. **The material RHS, the averaging order and the normalization.** These are unchanged from the reviewed prior body:
   - a shared uniform base, then m unconditional appended draws;
   - the center weight bounded by the exact Grassmann β, using α ≤ 1 at zero copies;
   - the low/high Fourier split, then Hölder with p/m ≥ 1, then per-level HC46 under finite Minkowski;
   - cross-level high-energy orthogonality, then the per-level Spectral47 bound;
   - an outer factor of 2 from `grassmann_le_twice_moment`.

   The new `selected_actual_analytic_rhs` is token-identical to the old one. The conditional Spectral47 premise is kept explicitly.

## 4. Findings

| ID | Sev. | Declarations | Evidence | Disposition and action |
|---|---|---|---|---|
| **H1** | **HIGH (custody)** | All 4 new files | The file headers give `D4B86B56…`, `03FB0A5D…`, `22DE415F…` and `AF3E380A…`. The native report's `added_object_hashes` give `6E8EA03C…`, `B472BC2E…`, `3268034A…` and `C02909B6…`. **All four differ.** Possible causes are CRLF/LF normalization, or the reviewed bytes being the Full94 binder repair rather than the captured objects. Since `hHC rfl` and the `_hEven` binders are present, the reviewed bytes look like post-repair bytes. | **Open.** It bars GO: I cannot tie my review to the profiled constants. Settle the hash convention, or supply the exact verified bytes, then re-confirm. |
| N1 | Medium (resolves the earlier HIGH I3/R5/I6) | SourceSize and Dyadic material roots | The `rows` binder is independent of `m`. For any total floor, `selector_unbounded` yields L and m with `hsel`, and an instance of any row count may be used. | **Resolved for the new roots, subject to H1.** The old roots keep the coupling, so they are non-claims for decoupled use. |
| N2 | Medium (resolved) | `…_at_dyadic_exponent` | `hklt` was never used in the prior proof (checked above). | **Resolved.** The ceiling is removed soundly. |
| N3 | Low | New-namespace duplicates of `HC46ExactContract`, `Spectral47ExactContract`, `selectedF`/`G`, `selected_actual_analytic_rhs` and others | The duplicates are linked only by delta-defeq. A future Spectral47 proof stated against either copy transfers only while the two bodies stay identical. | Document this, or make one copy an alias of the other. |
| N4 | Low (stale text) | The SourceSizeOriginalApplication header ("not compiled…"); the Dyadic header ("Uncompiled candidate"); an orphan `/-! Scalar right-hand side … -/` comment in the Dyadic file | These have no evidential weight either way. | Clean up before render. |
| N5 | Low (bookkeeping) | Native report | It gives `original_requested_axioms: 172` but `original173_requests_preserved: true`, and the 9 "added" roots include the Full90 export that was already among the 173. The total of 181 is consistent only if 172 + 9. | Reconcile the labels. I did not hand-count the 181-root list. |
| N6 | Info | Trace flags | `consumption_trace_complete: false`, `source_selection_complete: false` and `independent_body_review_complete: false` are self-reported. | Leave these open. |
| S1 | Medium, **open** | `Spectral47ExactContract` (both copies) | I re-derived the orbit argument by hand, including the column-space orbit count. It gives a ratio ∏(2^c−2^j)/(2^{c+s}−2^j) ≤ 2^{−is} and uses none of hEven, ρ, hc, hs or hHeight. The author's bounded receipt covers n ≤ 3 and d ≤ 4 only. The candidate `BinaryMatrixSameRangeOrbit` sits outside the frozen capture and is uncompiled. | Still a premise. Needs a machine proof plus a fidelity check against manuscript 4.7, which the formal contract is probably weaker than. |
| S2 | Medium, **open** | `selected_actual_analytic_rhs`, `hfail` | I re-checked the scalar note's algebra:<br>• coefficient `2^{1+m−2m/P}(r+1)^m 2^{500mr²P} ≤ Kinv`;<br>• with `a = 2^{−(2/3)rρh}`, the high term is `2^{r+1}a`, **if** B ≤ 2^{−r(s−1)}.<br>That condition still needs Parseval Σ_i E_i ≤ 1, s ≥ 2, and `3·2^{2h−2J} ≤ 2^{−r(s−1)−1}`. None of these is proved in Lean. Also r = 10m/ρ = 40000m³ must stay below 2h. | Numeric NO is **open**. Note that e = 1 makes `hfail` trivial. |
| S3 | Medium, open | `copies`, `U`, `A` | `U` is plausibly inhabitable through padding when rows > 0, via `taggedGoodU_nonempty_of_padding` in an unreached module. `A` exists as a complement. No joint witness is exhibited, and J is doubly exponential. | Joint-inhabitance witness, actual source arity and reduction gates. |
| X1–X5 | Carried | Complexitylib | Unchanged: no computability or runtime theorem; a `Classical.choose` base; existence-only sampling; tiny gap constants; a stale `Expander.lean` docstring. Only carrier data is reached. | Leave open for the reduction and runtime gates. |

## 5. Reconciling the 15 packet reports and 3 whole reports

- **Still resolved:**
  - export exactness (R1/I1/PA1-01);
  - hsmall/hdV derived, with the factor-2 direction correct (R2/I2/C3/P5-6);
  - HC46 non-vacuity (I2);
  - type identity (PA1-03).
- **Newly resolved, subject to H1:** the m/instance coupling (whole non-claims I3 HIGH, complexity R5, proof-adversarial I6, PA1-06), now resolved for the SourceSize roots, and the k < 8m obstacle to the manuscript's P.
- **Remains a non-claim:**
  - the untagged-center "vacuity" claim (cx-03 C1), already downgraded and still unreached;
  - the labelled-law and Rel acceptance results (C2/N1/N2/P3-2);
  - the unreached selection, incidence and expansion theorems (P3-1/PA4-01/N8);
  - `cut_expansion`, `kappa` and `hexpand` (PA4-02/P5-1).
- **Still open:**
  - Spectral47 (S1);
  - numeric NO and `hfail` (S2);
  - selector-L effectiveness, now without the instance-size issue;
  - J ≈ 2^{L^{Θ(log L)}} for reduction and runtime (R14 HIGH on that gate);
  - the E1 exponents and force-theorem m fidelity (R12/R13/C4-1, in unreached modules where m is still the instance index);
  - the `PseudorandomExact` one-sided 2e boundary (R17);
  - warning and linter suppression plus in-library `#print axioms` output (R15);
  - stale banners (R16);
  - the upstream seven-target post-audit and the CMMSA bridges (R19).

## 6. Safe conditional claim, valid only once H1 is resolved

Assume the pinned kernel and Init/Mathlib/Batteries trust, the 181 standard profiles, and identity reuse of the 319 prior bodies. Then for every `I : Instance N rows` with `rows` unrelated to m, every copies, U, A, C, T and f, every base and cutoff, and every L, `samplerA ≥ 1`, `r < c+s`, `e ≥ 0`, `hfail(e)` on the same coordinate leaf table, `Spectral47ExactContract cutoff`, `a > 0` and dyadic `k ≥ 4m`, where m is the selector output:

- `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)`;
- the center mass equals the exact Grassmann fraction;
- HC46 is discharged by the original inhabitant.

**Not claimed:**
- Spectral47 itself;
- a useful e, a, or numeric NO bound;
- a joint witness for I, copies, U and A;
- pre-draw selection or tables, or the actual source arity;
- the sampler, robust8S, the encoded reduction, runtime or learning;
- the CMMSA bridges;
- zero total warnings;
- manuscript acceptance.

## Remaining to-do

1. **H1:** reconcile the four new-file hashes with `added_object_hashes`, or supply the exact verified bytes. Then confirm the reviewed text matches them.
2. Fix the 172/173/181 labels (N5) and enumerate the reached constants for the four new modules.
3. Machine-prove the Spectral47 orbit identity against the actual append operator. Then remove `hSpectral` or keep it explicit, and audit fidelity to manuscript 4.7.
4. Prove a Parseval consumer (Σ E_i ≤ 1), the B ≤ 2^{−r(s−1)} side conditions, the finite-sum and scalar comparisons, and instantiate `base`/`cutoff`, r, T and P. Then compare 2·RHS with the NO threshold and prove `hfail` at a useful e.
5. Assemble a joint witness: rows > 0, padded copies, U, A, C, T and f at the selected m. Give an effective L₀.
6. Complete the source/star route: verifier acceptance → fixed f, pre-draw selection and tables, the actual sampler, and robust8S (`AllAmbientInverse`).
7. Handle the encoded reduction and runtime: doubly exponential J, explicit expander tables, `rotVal` cost, and the relation between L and the instance size.
8. Finish the upstream seven-target post-audit and build the CMMSA bridges.
9. Hygiene: deduplicate or alias the contract constants (N3), remove stale headers and comments (N4), dispose of warnings and linter suppression, and replay from a fresh checkout.
10. Manuscript fidelity (E1 exponents, constants, PR wording, the m role), then novelty and citation review, PDF QA and the final full-scope providers.
