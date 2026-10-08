# Proof-adversarial review: Full90 material-consumer packet 5/5

## Verdict: GO-WITH-NOTES for packet 5 only

**What this verdict covers.** It covers the 24 complete project files supplied in this packet. I read every body and skipped none. I found no soundness defect, vacuous main result, reversed inequality, or hidden added premise.

**What this verdict does not cover:**
- **No material verdict.** This packet does not contain `ActualSelectedComplementHC46OriginalApplication.lean`. I therefore did not verify the exact exported conclusion of `selected_actual_material_moment_bound_original` or its remaining guards (`hSpectral`, selector, failed-zoom, strict rank, positive parameters). That stays with integration. I did not substitute the selected-leaf wrapper or any easier surrogate for it.
- **No Complexitylib review.** No Complexitylib source file is in this packet. The Complexitylib boundary obligation is not discharged here (see §5).
- **No whole-manuscript verdict.**

**Method.** I used no tools, made no writes, ran no Lean or Lake, and spawned no subagents. Hashes, compile status and trace facts come from the supplied native qualification. I did not recompute them. Pinned Init, Mathlib and Batteries are trusted explicitly and were not reviewed. References are by declaration name.

## 1. Coverage (24 of 24 inspected, 0 skipped)

| # | File | Pinned `transitively_consumed` | Status |
|---|---|---|---|
| 1 | GaussianNearOne | false | inspected |
| 2 | GaussianRatio | false | inspected |
| 3 | GoodAdvice | false | inspected |
| 4 | GrassmannIncidence | false | inspected |
| 5 | **MatrixGrassmannIdentity** | **true** | inspected |
| 6 | **PortCycleReplacement** | **true** | inspected |
| 7 | PosteriorDensity | false | inspected |
| 8 | PosteriorReweighting | false | inspected |
| 9 | RobustSourceLineContainment | false | inspected |
| 10 | **SamplerParameters** | **true** | inspected |
| 11 | SamplerProximity | false | inspected |
| 12 | SubmoduleFunctionalGluing | false | inspected |
| 13 | SubspaceRestriction | false | inspected |
| 14 | **TaggedFinite3LinSource** | **true** | inspected |
| 15 | TaggedQuestionMassBridge | false | inspected |
| 16 | TripleRestrictionDimension | false | inspected |
| 17 | TripleRestrictionRank | false | inspected |
| 18 | VectorAdvice | false | inspected |
| 19 | WeightRounding | false | inspected |
| 20 | ZoomOutIncidence | false | inspected |
| 21 | ZoomOutJoint | false | inspected |
| 22 | ZoomOutParameters | false | inspected |
| 23 | ZoomOutPosterior | false | inspected |
| 24 | ZoomOutTransfer | false | inspected |

**Evidence tiers:**
- Only files 5, 6, 10 and 14 lie in the fresh 173-root closure. Even for these, only the constants actually reached carry standard transitive axiom evidence.
- The other 20 files are compiled but unconsumed. They have no axiom profile. Their theorems below are credited as reviewed source with compile evidence only.
- I found no `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `implemented_by` or `unsafe` in the supplied text.

## 2. Material-path files (the four consumed modules)

### MatrixGrassmannIdentity: the copies, α, and the matrix/Grassmann moment identity
- **Definitions are actual counts.**
  - `rankProbability n d w = ∏_{i<w}(1 − 2^{d+i}/2^n)`. This is the exact probability that w uniform vectors extend a fixed independent d-frame (`rankArray_ratio`, `rankProbability_count`).
  - `alpha n d w t = P(M full rank) · P(extension)^t`.
  - `rankEventProbability_eq_alpha` derives α as the probability of the actual joint rank event over all t copies. It is not assumed.
- **`matrix_grassmann_identity`** (premise `d+w ≤ finrank V`) states `matrixMoment = alpha · grassmannExperiment`. I re-derived it:
  - Rank-deficient M contribute 0 (`hbad`).
  - Frames factor through `sum_over_frames` with multiplicity `frameProduct d d`.
  - `base_rank_ratio` converts `|Grass|·frameProduct/|arrays|` into `rankProbability n 0 d`.
  - `iid_mean_power` matches the t independent containing-space copies to `aboveMean^t`. It is exact, including t = 0.
- **Direction available to the consumer.** From `alpha_bounds` (α ∈ [0,1], given `d+w ≤ n`) and `grassmannExperiment_nonneg`, matrixMoment ≤ grassmannExperiment holds with no size premise.
- **Reverse direction is conditional.** `grassmann_le_twice_moment` needs `hsmall`.
- **`alpha_loss_bound` is correct.** The steps are:
  - 1−ab ≤ (1−a)+(1−b);
  - 1−p^t ≤ t(1−p);
  - each factor loses at most w·2^{D−1}/2^n with D = d+w > 0.
  
  The case d+w = 0 is handled separately (`grassmann_le_twice_moment_zero_dimension`).

### SamplerParameters
- `blocks A h = 2^(2^(A h²))` and `beta = A h²/blocks`.
- `beta ∈ [0,1)` and `blocks·beta = A h²` (`mean_rat`, `mean_real`) are proved.
- The zero cases A = 0 and h = 0 are explicit.
- The tail theorems delegate to `DropTailParameters` (not in this packet, pinned unconsumed). That suggests only `blocks`/`beta`-level constants are reached here. Integration should confirm.

### TaggedFinite3LinSource (source copies)
- `taggedCopy` puts K disjoint copies on `Fin K × Row` / `Fin K × Var`. `row_injective` lifts correctly.
- `taggedCopy_violations` is exact additivity over copies.
- `taggedCopy_repeatAssignment_violations = K · violations` is exact.

### PortCycleReplacement (coordinate rotation tables)
- **`rotation_involutive` holds.** Label 0 uses the involution `R`. Labels 1 and 2 swap forward and backward cycle steps. Degrees 1 and 2 are covered: at degree 1 the cycle edges are a self-loop pair.
- **`cut_decomposition`** gives `cut = external + cycles`, re-derived exactly.
- **`cut_expansion`** concludes `h/((d+1)(d+2+h)) · smallSide S ≤ cut R S`. I re-derived it from:
  - `smallSide_transport`;
  - `external_transport` (the perturbation inequality summed along the bijection `R`);
  - `discrepancy_le_cycles` (`minority_le_cycle`: a nonconstant cloud has a cycle crossing ≥ 1, and minority ≤ d+1).
  
  The constant is weak but valid.
- **`graph_degree = 3`** and **`graph_order = n(d+1)`** hold through `change` to `Fintype.card`. These depend on the Complexitylib definitions `RegGraph.deg` and `RegGraph.order`.

## 3. Unconsumed files: audit summary (no axiom evidence)

**Gaussian ratio files.** `gaussian_ratio_eq`, `gaussian_ratio_le` (≤ 2·2^{a(n−m)}), `gaussian_near_one` and `error_le_inverse_pow` are exact or correctly oriented. `normalizedFrame_ge_half` needs `a+1 ≤ n`. Natural subtraction is guarded by explicit `≤` premises.

**Triple restriction files.**
- `blockMass` sums to 1, with drop probability β.
- `badRows_probability ≤ (2^c−1)β` is a genuine union over nonzero coefficient vectors, using one non-kept coordinate per nonzero row combination.
- `goodRows_intersectionCodim` derives codimension c from dual-map surjectivity.
- `retained_finrank_add_twice_dropCount` is an exact identity.

**SubspaceRestriction.** `definingForms_kernel` (ambient kernel = W) uses the whole annihilator. `arbitrary_subspace_failure_probability` is unconditional, and its docstring correctly says W is fixed and makes no posterior-independence claim.

**PosteriorReweighting.** These are generic finite Bayes identities. In `normalized_reweighting` I re-derived the bounds Z ≥ p0/2, the bad mass ≤ 2ζ/p0, and the mean error ≤ 4η + 4ζ/p0. Null-marginal posteriors evaluate to 0; they are not a normalized law.

**PosteriorDensity.** `conditional_density_le ≤ 8·2^{2aT}` uses the good-marginal premise, `retained_finrank_lower` and the Gaussian ratio cutoff.

**SamplerProximity.**
- `eventually_ready` holds because 4(A + 4r + 212)h⁴ dominates every term of `Ready`.
- I re-checked these consequences of `Ready`: `ready_advice` (≤ 2^{−100h²}), `ready_zoom(_scaled)`, `ready_small_beta`, `ready_density` (≤ 2^{−30h²}), `ready_dimensions` and `five_decay70_lt`.

**GoodAdvice.**
- `ready_fixed_rank_failure ≤ 2ζ` follows from the density bound (≤ decay 30) plus tailMass ≤ ζ.
- `eventual_good_advice` rests on A > 0 and on external lemmas from AdviceExceptions, ConditionedCovering and CoveringSpan (not in this packet).

**ZoomOut chain.**
- **ZoomOutIncidence:** `retainedZoomMass_ratio` is exact flag counting.
- **ZoomOutParameters:** the `dimension_budget` omega facts follow from 2(2h+r+1) ≤ J.
- **ZoomOutPosterior:**
  - `zeta_div_le_decay20` needs (2h−a)c ≤ 10h², which holds because c ≤ r < h.
  - `numerical_small` holds: 12·decay20 < decay12.
  - `ready_comparison` instantiates reweighting with ζ' = 2ζ correctly.
- **ZoomOutTransfer:**
  - `condition_tv_mul_le` (P(E)·TV_cond ≤ 2TV) is consistent with tv = ½L¹.
  - `exact_disintegration` is exact.
  - `total_error_small` holds: 8·decay10² + decay10·decay2 < decay10.
- **ZoomOutJoint:**
  - `score_threshold`: mean ≥ C/2 gives mass ≥ C/4.
  - `ready_posterior_success`: C/4 − 2ζ ≥ C/8 holds under 16ζ ≤ C.
  - Bayes reordering is used only on favorable (good) advice, which has positive marginal.

**VectorAdvice.** On success the output is exactly the uniform span (`conditional_output_uniform`). Dependence fails explicitly rather than resampling. `joint_score_loss` gives 0 ≤ ideal − actual ≤ 2^r/2^J.

**WeightRounding.**
- `rounding_complete` and `rounding_budget_transfer` hold: k·(9t/8) ≤ (σ/2)(9t/8) < σt.
- `dyadicScale_upper < 16(N+1)/t` holds for t ≤ 1.
- `polynomial_denominator_bound ≤ 17(n+1)^{k+1}` holds.

**SubmoduleFunctionalGluing.** Existence and uniqueness of the glue on A ⊔ B are correct, and the result is independent of the chosen decomposition.

**TaggedQuestionMassBridge.**
- `taggedCopy_rowConflict_iff` (same tag ∧ base conflict) is checked in both directions, including the case of a shared third row.
- Bad mass ≤ J(J−1)C/(K·|Row|), with J = 0 and K = 0 handled.

**RobustSourceLineContainment.**
- `nontrivial_inf_iff_quotientImages` needs Q ≤ L and Q ⊓ H = ⊥, and both are used.
- The union bound over lines inside H holds, and the dyadic bound (2^j−1)(2^d−1)/(2^n−1) ≤ 2^{−(n−j−d−1)} holds.
- The interval version goes through the quotient equivalence.

## 4. Findings

| ID | Sev. | Declarations | Disposition | Remaining action |
|---|---|---|---|---|
| P5-1 | Medium (integration) | `cut_expansion`, `hexpand`, `cut`/`external`/`smallSide`; Complexity.RegGraph | Sound as a conditional local-cut transfer. `hexpand` is the project's own unnormalized vertex/edge-cut expansion (non-loop rotation orbits counted once). Nothing here connects it to any Complexitylib spectral or edge-expansion notion, or to `ExpanderFamily`. The header correctly lists spectral-to-cut and FP instantiation as separate. | Integration must show where `hexpand` is discharged, reconcile degree normalization with Complexitylib, and confirm which PortCycleReplacement constants the material root reaches. Do not prove expander interfaces by citation. |
| P5-2 | Medium (non-claim) | `ready_joint_success`, `eventual_joint_success` | Conditional on the external decoder premise `hdecoder`, as the docstrings say. Not consumed and has no axiom profile. | Must not be cited as decoder existence or a robust result. |
| P5-3 | Low (provenance) | Banners in GaussianNearOne, GaussianRatio, GoodAdvice, GrassmannIncidence, MatrixGrassmannIdentity ("await compilation"), PortCycleReplacement ("not compiled"), PosteriorDensity, SamplerParameters, SamplerProximity, TripleRestrictionDimension, VectorAdvice, ZoomOut×5; "author exports passed / review pending" in SubspaceRestriction and TripleRestrictionRank | The banners contradict the 319-file compiled closure and carry no weight in either direction. | Clean up before render. |
| P5-4 | Low (hygiene) | Files relying on auto-bound implicits: GaussianNearOne, GaussianRatio, GrassmannIncidence (`J`, `a`), PosteriorDensity, TripleRestriction*, SubspaceRestriction, GoodAdvice (`a` in `bad`), RobustSourceLineContainment (`j`, `a`) | Each auto-bound name I checked only generalizes its statement. I cannot rule out every misspelling being silently bound. | Add `autoImplicit false`. |
| P5-5 | Info | MatrixGrassmannIdentity `rawTF_frame`/`hG` (`rfl` against `extensionTest`), `respectTransparency false` | Elaboration-only reliance on definitional equality. The kernel rechecks. | Replay note. |
| P5-6 | Info (scale) | `blocks A h = 2^(2^(A h²))` | Ambient dimension is doubly exponential in h. No runtime or encoding claim is made here. | Encoded-reduction and runtime gates must account for it. |
| P5-7 | Info | `bayes_ratio`, `condition_null`, `posteriorMixture` | Null events evaluate to 0. `conclusion_mass_defect` honestly bounds the resulting mass loss. | — |
| P5-8 | Info | `retained_gaussian_ratio_le` (4 where 2 suffices), `score_tv_le` (2·tv), `cut_expansion` constant | Loose but valid. | Manuscript constant fidelity. |
| P5-9 | Info | `polynomial_denominator_bound` | Conditional on 1/t ≤ (n+1)^k, which the caller supplies. Not a runtime claim. | — |

## 5. Complexitylib boundary
- This packet contains **zero** of the 23 Complexitylib files.
- The only Complexitylib dependence here is `graph`, `graph_degree` and `graph_order` in PortCycleReplacement. They use the `RegGraph` structure fields and its `deg`/`order` definitions. `cut_expansion` itself uses no Complexitylib content.
- I did not review Complexitylib representations, padding/reindexing, sampling, quantified family hypotheses or computational bounds. I treated none of them as previously reviewed.
- The Complexitylib boundary obligation therefore remains **OPEN** for whichever packet carries those bodies, and for integration.

## 6. Cross-packet questions
1. **Exact material export.** Check the exported conclusion of `selected_actual_material_moment_bound_original`: that it uses the same `Tc`/`fc`/`r`/η = 2e, removes only `hHC`, and keeps `hSpectral`, selector, failed-zoom, strict-rank and positivity premises. Also check where it discharges `d+w ≤ finrank V` for `matrix_grassmann_identity`/`alpha_bounds`.
2. **Per-constant reach.** List the constants of MatrixGrassmannIdentity, PortCycleReplacement, SamplerParameters and TaggedFinite3LinSource that the material root reaches, and the route (for example FixedPortCycleFamily or the Cmmsa reconciliation).
3. **External bodies used here.** These must be reviewed in their own packets:
   - DropTailParameters / DropCountTail;
   - AdviceExceptions, ConditionedCovering (`tv`, `fibre_conditional_tv_le`, `deletedConditional_eq_advicePosterior_mixture`), CoveringSpan, CoveringTV;
   - GrassmannFlagPosterior / GrassmannCounting (`incidenceCount_eq`, `card_relativeUpper`, `flag_product`);
   - MatrixGrassmannFibre/Moment (`card_rankArray`, `sum_over_rankArrays`, `uniform_extension_law`);
   - FiniteSampling, Formula, ActualFinite3LinSource;
   - ActualQuestionMassBridge (`bad_ordered_question_count_le_of_conflict`), ActualBinaryGrassmannSamplingBounds.
4. **Complexitylib and the cut premise.** Supply the Complexitylib bodies and the discharge of `hexpand` (P5-1).

## 7. Safe conditional claim

Under the pinned kernel and library trust and the qualified native receipts, the four consumed modules in this packet prove the following without hidden premises:
- the exact identity `matrixMoment = α · grassmannExperiment`, with α the actual joint rank-event probability in [0,1];
- the sampler parameter facts;
- exact tagged-copy violation additivity;
- conditional port-cycle cut transfer, under the local premise `hexpand`.

The 20 unconsumed modules are sound as reviewed source but carry compile evidence only, with no axiom profile.

**Not claimed:**
- material-moment acceptance or the exact export statement;
- Spectral47 or a useful numeric NO bound;
- expander, Complexitylib, source, star or robust8S results;
- decoder existence;
- reduction, runtime or learning results;
- upstream, warning, fresh-checkout, provider or manuscript gates.
