# Non-claims integration review: Full95 new bodies and whole-material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **Native and material conditional integration** of the 4 new bodies, read against the actual material lane | **GO-WITH-NOTES.** No unresolved HIGH finding in this scope. |
| **Unconditional material readiness** | **NO.** Spectral47 is still a premise. There is no packaged witness that all the premises can be satisfied together. No useful `e` or numeric NO result exists. |
| **Overall full-goal GO, theorem readiness, manuscript readiness** | **Not issued.** Gates outside the material scope are still open, including the earlier complexity finding R14, which is HIGH (reduction/runtime). No publication or novelty acceptance is given. |

**How I worked.** No tools, writes, Lean/Lake runs or subagents. I recomputed no hashes. Native facts come from the supplied qualified report and trace: 7 stage exits of 0, 181 requested profiles all standard, 323 sources, 8069/8069 trace edges, and both graphs fully resolved. I treated the three author notes as hypotheses. A native GREEN is taken as kernel acceptance only, not as semantic acceptance.

## 1. Coverage

**Supplied complete bodies: 67. Inspected: 67. Skipped: 0.**

- **4 new bodies, read line by line.** Every declaration in each was checked against its predecessor:
  - `ActualSelectedComplementSourceSizeAppendMoment` (SHA D4B86B56…)
  - `ActualSelectedComplementSourceSizeAnalyticMoment` (SHA 03FB0A5D…)
  - `ActualSelectedComplementSourceSizeOriginalApplication` (SHA 22DE415F…)
  - `ActualSelectedComplementManuscriptDyadicMoment` (SHA AF3E380A…)
- **40 prior project bodies, read in full.** I re-derived only the steps the new bodies actually consume. Everything else rests on the prior reviews, whose identities were verified, and I saw nothing new in it.
  - The 5 critical files: HC46OriginalApplication, AnalyticMoment, AppendMoment, OriginalExactInhabitant, LeafLabelRankImageAlignment.
  - The 35 reached modules: AppendFourierCrossLevelOrthogonality, BinaryGrassmannSamplingBounds, CmmsaAdmissibilitySelector, CmmsaParameterReconciliation, ComplementCoordinateMassBridge, EqualityCloud, Finite3LinSource, FiniteLaw, FiniteMomentLpBounds, FixedFunctionalAppendOperator, FixedFunctionalBinaryMatrixMoment, GraphEdges, OccurrenceAllocation, OrdinaryStarMatchingFiber, OrdinaryStarWeightedSelection, RankImageRightBasisInvariance, RhsFunctionalConstruction, SelectedSpectralParameters, StarFixedRhoDimensionGuard, StarQuestionSupport, StarSpanIntersection, TaggedComplementIncidence, TaggedComplementStarDensityBridge, TaggedConcreteStarLaw, TaggedFixedCenterGeometry, TaggedFixedTableAcceptance, TaggedOrderedSampleNonempty, CoveringSpan, CoveringTV, EqualityGadget, FixedPortCycleFamily, MatrixGrassmannIdentity, PortCycleReplacement, SamplerParameters, TaggedFinite3LinSource.
- **23 Complexitylib bodies, read.** They are unchanged since the earlier boundary review; the CX-/X-/N- findings carry over.

**Not supplied, so not reread.** The remaining 279 of the 319 unchanged prior bodies are credited only through identity reuse: identical bytes, configuration, constant types and proof edges (7979 shared). Reuse is not a reread, and it does not accept the new integration semantics. Examples include ActualSourceStarLaw, ActualFixedFunctionalStarMoment, ActualFixedFunctionalMatrixLift, MatrixLiftNominalDirectComparison, the A7–A22/DR6/RealQ chain, ActualTaggedOrderedQuestionSourceBridge, ActualMaximalPairLadder, and MatrixGrassmannFibre/Moment.

## 2. New declarations, complete list

**SourceSizeAppendMoment**
- Private: `selected_rankloss_exponent`, `rankloss_from_exponent`
- `selected_actual_append_moment`, `selected_actual_center_identity`

**SourceSizeAnalyticMoment**
- Contracts: `HC46ExactContract`, `Spectral47ExactContract`
- Selected functions: `selectedF`, `selectedG`, `selectedLevel`, `selectedLowIndexSet`, `selectedLow`, `selectedHigh`, `selectedHighFin`, `selectedHighFinIndexSet`
- Leaf lemmas: `selected_leaf_indicator_basis_invariant`, `selected_leaf_HC46_of_exact_PR`, `selected_leaf_failed_zoom_PR`
- Fourier split and append averaging: `selectedHighFin_eq_selectedHigh`, `selectedHighFin_eq_finset_sum`, `rankProjection_finite_reconstruction`, `selected_append_low_high_decomp`, `appendAverage_finset_sum`, `appendAverage_abs_pow_le`, `appendAverage_lpMoment_le`, `lpMoment_le_pow_of_lpNorm_le`
- HC46 low part: `selected_leaf_append_level_HC46`, `selectedLowHC46NormBound`, `selected_low_append_HC46_lpNorm_bound`
- Moment and threshold: `selectedActualMoment`, private `pow_add_le_two_pow`, `appendAverage_indicator_mem_unit_interval`, `actual_append_threshold_pointwise`, `actual_append_threshold_mean_bound`, `exists_dyadic_exponent_for_actual_moment`, `actual_append_threshold_mean_bound_beta`, `selected_low_weighted_holder`
- Center beta and event bounds: `selected_center_matrix_mean_le_exact_grassmann_beta`, `selected_actual_event_moment_bound`, `selected_actual_event_moment_holder_bound`, `selected_actual_reconstructed_holder_bound`, `selected_actual_moment_def`
- High part and spectral: `appendHighLevel_energy_eq_sum`, `appendHighLevel_energy_le_spectral_sum`, `selected_leaf_high_energy_le_spectral`
- Exponents and assembly: `real_pow_moment_div_m_eq_pow`, `exists_dyadic_moment_exponent_window`, `selected_actual_HC_spectral_moment_bound`, `selected_actual_analytic_rhs`, `matching_center_mass_eq_grassmann_beta`, `selected_actual_source_dimension_bound`, `selected_actual_material_moment_bound`

**SourceSizeOriginalApplication**
- `selected_leaf_HC46_original`, `selected_leaf_failed_zoom_HC46_original` (both compile-only, not roots)
- `selected_actual_material_moment_bound_original`

**ManuscriptDyadicMoment**
- `selected_actual_HC_spectral_moment_bound_at_dyadic_exponent`
- `selected_actual_material_moment_bound_at_dyadic_exponent`
- `selected_actual_material_moment_bound_original_at_dyadic_exponent`

## 3. Checks on the requested points (independent)

**Same objects throughout.** Every new export takes the binders I, copies, U, A, C, T, f, base, sourceHeightCutoff, hsel, hA, r, hrd, e, he, hfail, hSpectral, a and ha.
- From these it builds one coordinate set: `Cc = selectedCoordinateCenterTable`, `Tc = selectedCoordinateLeafTable`, `fc = coordinateFunctional`.
- That same `Tc` is used in `hfail`, in the PR premise (`actual_leaf_failed_zoom_gives_nominal_pseudorandom … Tc fc`), in the moment, and in the RHS.
- The source and star instance is unchanged: the star mass is on `A.1` with `transportedCenterTable` and `transportedLeafTable`.
- There is no selected-leaf surrogate. The `selected_leaf_*` wrappers are not on the export path.

**m is the leaf query count, separate from the source row count.** The instance type is now `ActualOccurrenceAllocation.Instance N rows`, and `rows` appears only there. `m` plays exactly three roles:
- the selector output (`hsel`);
- the star arity (`matchingStarMass (m := m)`, where k := m in the append moment);
- the rank-loss term (`c + m*s + 2h ≤ 2J`, which uses the arity, as it should).

This removes the coupling flagged in the earlier non-claims I3 and complexity R5 findings. It agrees with the native flag `source_row_independence_native_verified`.

**SourceSize dimensions.** The relevant quantities are h = `hBlock L m`, J = `blocks samplerA h`, c = `leafT m h`, s = `leafK m h`, and n = 2J.
- `sideComplement_finrank` gives dim A = 2J.
- `selected_rankloss_exponent` gives c + s = 2h ≤ 2J. It also gives `hsmall` (rank loss ≤ ½), which is derived rather than assumed. Neither is an export premise.

**Caller floor `analyticSourceHeightFloor`.**
- The selector floor is `max (analyticSourceHeightFloor base cutoff j) (j+2)`. In AppendMoment this matches `sourceHMin := analyticSourceHeightFloor base cutoff` through beta-reduction.
- `selected_spectral_parameters` yields `cutoff(actualSelectedRho) ≤ h` at ρ = 1/bOf m. That is the same cutoff carried by `hSpectral`.
- Both `base` and `cutoff` are chosen by the caller. Nothing instantiates them with the quantitative cutoffs from the scalar note.

**Height, rank and dimension guards.**
- `hrd : r < c+s` is still required.
- `hdim : c+s ≤ n` is derived.
- `hkm : 4m ≤ k` gives both `4 ≤ k` (because m ≥ 256) and `k/m ≥ 1`.
- No guard is weakened.

**HC46 discharge.**
- `SourceSizeOriginalApplication…original` is a single `exact … original_HC46_exact hSpectral a ha`.
- `…original_at_dyadic_exponent` passes the fully qualified `ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact`.
- Only `hHC` is removed. The remaining binder lists are identical to their non-original counterparts.

**Dyadic exponent chosen by the caller.**
- In the fixed-window predecessor `selected_actual_HC_spectral_moment_bound`, the binder `hklt : k < 8m` is never used in the proof body. Dropping it is therefore sound.
- The new proof is otherwise a step-for-step copy.
- The cost of a large k shows up in the RHS as 2^{500 i² k m}, so there is no free lunch.
- `k` is an implicit binder that `hkDyadic`/`hkm` pin down. That is fine; callers can still write `(k := _)`.

**The material RHS, and the order and normalization of averaging.** I verified the chain:

> star mass (uniform center, then independent uniform leaves) ≤ 2 · `uniformMean_M[1_G(M) · appendAverage(1_F)(M)^m]`

- In that moment there is one shared base, m unconditional appended draws, and normalization by card. Rank-deficient matrices score 0.
- The RHS is 2^m·β^{1−m/k}·S_k^m + 2^m·a^m·β + (1/a²)·Σ_{i>r}(2^{−i(s−1)} + 3·2^{i−n})·E_i.
- β is the exact Grassmann center fraction on `Fin(2J) → ZMod 2`.
- The center identity is an equality.

**Spectral assumption is kept, unchanged.** `SourceSizeAnalyticMoment.Spectral47ExactContract` is alpha-equivalent to the old contract; only binder names gain underscores. It is still an explicit premise.

## 4. Findings on the new declarations

| ID | Severity | Declaration(s) | Finding | Disposition and action |
|---|---|---|---|---|
| F1 | Resolved | `SourceSizeOriginalApplication.selected_actual_material_moment_bound_original`, `…original_at_dyadic_exponent` | Exactly `hHC` is removed; conclusions and guards are identical; profiles are standard. | Credit as a conditional material bound. |
| F2 | HIGH → **Medium** (formerly I3/R5) | all SourceSize exports | The coupling is gone structurally. What remains: no packaged witness shows that I (rows ≥ 1), copies, `U : TaggedGoodU … J`, A, `hsel`, and `hSpectral` can all hold at once. My reasoning (not proved): `selector_eventually_exists` supplies m, padding copies (`taggedGoodU_nonempty_of_padding`, not reread here) supply U, A comes from `exists_isCompl`, and `e = 1` satisfies `hfail`. | Prove a joint-inhabitance lemma, with Spectral47 kept as the only premise or discharged. |
| F3 | Low | `SourceSizeAnalyticMoment.HC46ExactContract` / `Spectral47ExactContract` | These are new constants that duplicate the old ones. `original_HC46_exact` is typed at the old contract, and the kernel accepted it by delta/alpha defeq. | Any future Spectral47 proof must target the SourceSize constant, or prove the two equal. Record both in the trace. |
| F4 | Low (claim hygiene) | Old `HC46OriginalApplication.selected_actual_material_moment_bound_original` and the old AnalyticMoment/AppendMoment | These remain roots and still carry `Instance N m`, i.e. the coupling. | Mark them superseded. Cite only the SourceSize or dyadic exports. |
| F5 | Info | `…at_dyadic_exponent` | "Manuscript" in the name does not mean manuscript fidelity. With k unbounded, the RHS worsens as k grows. | Use the name only together with a calibrated choice of k. |
| F6 | Low | Docstrings in SourceSizeOriginalApplication ("has not been compiled"), ManuscriptDyadicMoment ("Uncompiled candidate"), and SourceSizeAnalyticMoment (`hdecomp` is the "sole remaining obligation", and contracts "not proved locally" now stale for HC46) | Stale. They carry no weight either way. | Clean up before render. |
| F7 | Info | Native report | The old export is listed under "added" (172 + 9 = 181, versus the earlier 173). This is consistent bookkeeping, not a defect. | Note it in custody. |
| F8 | Info | `let : Nonempty …` (instead of `letI`), `_h*` renames, `simp` set changes | Affects elaboration only. Zero owned warnings is partly achieved by renaming. | Handle under the warning gate. |

## 5. Author notes (bounded evidence, not certificates)

**Scalar calibration.** I re-derived the algebra:
- Σ_{i≤r} 2^{500i²P} ≤ ((r+1)/2)·2^{500r²P} holds for r ≥ 2 and P ≥ 4.
- The low coefficient 2·2^m·((r+1)/2)^m·2^{m−2m/P} ≤ K_inv.
- The exponent directions hold for β, e ≤ 1: β^{1−m/P} ≤ β^{1−1/T} and e^{m−2m/P} ≤ e^{m−2/T}.
- With a = 2^{−(20/3)mh}, B ≤ 2^{−r(s−1)} matches 2^r·a³ exactly.

What remains open:
- (a) A ρ-faithful r = 10m/ρ = 40000m³ forces `hrd`, i.e. h > 20000m³. The caller floor must impose this; nothing else does.
- (b) The high-energy bound needs Σ E_i ≤ 1 (Parseval normalization), which is not proved in this scope.
- (c) The comparison against the actual selection lower bound (`exists_weighted_matching_functional` scale) has not been made.
- (d) K_inv is about 2^{Θ(m^{10})} or larger, which makes the height astronomical.

Numeric NO stays **open**.

**Spectral orbit gain.** This is bounded evidence (n ≤ 3, d ≤ 4) and agrees with the earlier reviewer sketches. It is still not a universal proof. The orbit helper sits outside the Full95 capture and is uncompiled. Spectral47 stays **open**, and its fidelity to manuscript 4.7 is unaudited. The hypotheses hc, hs, ρ and hHeight appear unused, which suggests the contract is weaker than 4.7.

**Citation scope.** One new fidelity flag: MZ Theorem 3.1 gives completeness 1 − η, not perfect completeness. This affects the source and YES gates, not the material bound.

## 6. Reconciling the 15 packet reports and 3 whole reports

| Prior cluster | Status now |
|---|---|
| Export exactness and HC46 vacuity (I1, I2, R1, PA1-01/03) | Resolved, and still resolved for the new exports. |
| `hsmall`/`hdV`/factor-2 direction (I2, R2, C3, P5-6, C5-10) | Resolved; re-derived in SourceSizeAppendMoment. |
| m coupling (non-claims I3 HIGH, complexity R5, proof-adversarial I6) | Structurally resolved for SourceSize exports; downgraded to F2 (joint witness, Medium). The old export keeps the coupling (F4). |
| Selector hitting a prescribed m (R4, I5) | Moot for the decoupled exports, since m is now existential in practice. No effective L₀ yet (Low). |
| Spectral47 (PA1-04, cx-01 P2, I4/I5/R3) | Open. |
| Numeric NO and `hfail` usefulness (PA1-05, I9/I11/R10, P4) | Open; the scalar note narrows it (§5) but does not certify it. |
| Untagged-center vacuity (cx-03 C1, I4/I7/R6) | Remains Info/non-claim; unreached. |
| Acceptance, selection and star theorems unreached (P3-1, PA4-01, N1/N2, I8/R8) | Unchanged. The source/star/robust8S gate is open. |
| Complexitylib (X1–X5, N3–N8, CX-01–05, I9/I10/R9) | Unchanged. Carrier data only; no runtime, explicitness or constants. |
| R14 HIGH (doubly-exponential J versus reduction/runtime) | Open, outside the material scope. Bars overall GO. |
| E1 47/127/216 versus 75/150/225 (N5, R12) | Open fidelity item. |
| Stale banners, `#print axioms` in library modules, linter suppression (I12–I15, R15/R16) | Open hygiene; joined by F6 and F8. |
| Upstream seven-target selected profiles (I16, R19) | Not CMMSA bridges; post-audit pending. |

## 7. Safe conditional claim

This rests on the pinned kernel and Init/Mathlib/Batteries trust, the Full95 qualified receipts (181 standard profiles, 323 sources), and identity reuse of the 319 prior bodies.

> **`SourceSizeOriginalApplication.selected_actual_material_moment_bound_original`.** Take any `I : Instance N rows` with `rows` independent of m, together with copies, U, A, C, T and f. Suppose the selector at the caller floor returns m, and that `1 ≤ samplerA`, `r < c+s`, `0 ≤ e`, `hfail(e)` on the same `Tc`, `Spectral47ExactContract(cutoff)` and `a > 0` all hold. Then:
> - there is a dyadic k with 4m ≤ k < 8m such that `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)`;
> - the center mass equals the exact Grassmann fraction.
>
> **The dyadic variant** gives the same conclusion for every caller-chosen dyadic k ≥ 4m.
>
> In both, HC46 is discharged by `original_HC46_exact`.

**Not claimed:**
- Spectral47 or its fidelity to 4.7;
- joint inhabitance of the premises;
- a useful e or a, or numeric NO;
- source, star or robust8S results, or acceptance-to-functional;
- expansion, FP, runtime, learning or encoded reduction;
- upstream bridges;
- zero total warnings or a fresh checkout;
- novelty, citations, render, or manuscript acceptance.

## Remaining to-do

1. Prove a joint-inhabitance lemma (F2) for I (rows ≥ 1), padded copies, U, A, `hsel` and `hfail`.
2. Retire or mark superseded the old m-coupled exports (F4). Settle which contract constant is canonical (F3).
3. Machine-prove the Spectral47 orbit identity for the SourceSize contract, or keep it as an explicit premise. Audit fidelity to manuscript 4.7.
4. Certify the scalar calibration in Lean:
   - a caller floor enforcing h > 20000m³, the T and P choices, and the λ and α height conditions;
   - the Parseval bound Σ E_i ≤ 1;
   - the finite-sum estimate;
   - the comparison with the actual weighted-selection lower bound. Then prove `hfail` at the required e on NO instances.
5. Source, star and robust8S: on the trace, establish tagged acceptance → ordinary density → selected f. Prove `AllAmbientInverse`. Reconcile completeness 1 − η.
6. Encoded reduction and runtime (R14 HIGH): handle the doubly-exponential J, explicit expander tables and `rotVal` cost. Make no runtime claim based on Complexitylib.
7. Complete the independent post-audit of the upstream seven targets, then build the CMMSA bridges.
8. Hygiene: stale docstrings (F6), warning and info-log disposition (F8, I13/R15), and a fresh-checkout replay.
9. Manuscript fidelity (E1 exponents, constants, PR wording, the m/rows semantics), then render, novelty, citations, BibTeX/PDF QA and the final full-scope providers.
