# Non-claims review, packet 5/5: Full90 material consumer

**Verdict for this packet: GO-WITH-NOTES.**

This verdict covers only the 24 project files in this packet. It is not a verdict on the material review, the integration or the manuscript. I used no tools, made no writes and ran nothing (no Lean, no Lake). The native facts I rely on (seven zero exits, the 173-root standard-axiom stdout, 319 pins, consumption flags) come from the packet as supplied; I did not recompute any hash. Findings cite declaration names rather than line numbers.

**Complexitylib.** None of the 23 Complexitylib context files was supplied in this packet, so none was skipped here. It also means this packet does not perform the Complexitylib boundary review. That obligation stays open unless another packet's reports cover all 23 bodies. The only project-side Complexitylib use in this packet is `PortCycleReplacement`'s import of `Complexitylib.Classes.PCP.Internal.Expander`. I audited it below.

**The material export.** `ActualSelectedComplementHC46OriginalApplication.lean` is not in this packet, so I cannot check the statement or guards of `selected_actual_material_moment_bound_original` here. The stdout confirms only its axiom profile (`propext, Classical.choice, Quot.sound`). That its conclusion and guards are exact, with only `hHC` removed, stays an integration item.

## 1. File inventory

All 24 files were inspected in full; none was skipped.

| # | File | Consumed pin | Status |
|---|---|---|---|
| 1 | GaussianNearOne | false | inspected |
| 2 | GaussianRatio | false | inspected |
| 3 | GoodAdvice | false | inspected |
| 4 | GrassmannIncidence | false | inspected |
| 5 | **MatrixGrassmannIdentity** | **true** | inspected (material-critical) |
| 6 | **PortCycleReplacement** | **true** | inspected (Complexitylib boundary) |
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

In the supplied text there is no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` or `opaque`. `decide` appears only on closed `Fin`/`Nat` facts.

## 2. Material-critical and consumed files

### MatrixGrassmannIdentity (consumed)

- **`matrix_grassmann_identity`** is exact and holds for every `Rset`, `Lset` and `t`, under the single guard `h : d+w ≤ finrank V`.
  - Statement: `matrixMoment = alpha · grassmannExperiment`.
  - I re-derived it. A uniform M is independent with probability `rankProbability n 0 d` (`base_rank_ratio`), and given that, its span is uniform. Each extension is independent with probability `rankProbability n d w`, and given that, the extended span is uniform on `Above R w` (`normalized_extension_law`).
  - Dependent M scores 0 (`rawF_deficient`, `deficient_integrand`), so nothing is resampled.
- **Copies.** The t copies are genuinely t independent extension arrays of the same M (`matrixExperiment_eq`), and on the Grassmann side t independent uniform spaces above the same R (`grassmannExperiment_eq`, `iid_mean_power`). `alpha` is shown to equal the probability of the actual joint rank event (`rankEventProbability_eq_alpha`); it is not a stipulated constant.
- **Direction.** `alpha_bounds` gives `0 ≤ alpha ≤ 1`, so matrixMoment ≤ Grassmann experiment needs no size premise. The reverse factor-2 bound (`grassmann_le_twice_moment`) is conditional on the caller-supplied `hsmall`, i.e. `(d+tw)·2^(d+w−1)/2^n ≤ 1/2`. I re-derived `alpha_loss_bound` (the base and extension union bounds, plus 1 − ab ≤ (1−a)+(1−b)).
- `rawTF_frame` closes by `rfl`, so it relies on `extensionTest` and `rawF` being definitionally equal (defined in MatrixGrassmannFibre/GrassmannCounting). The build supports this; it should not be read as a separate semantic fact.

### PortCycleReplacement (consumed; the only Complexitylib consumer here)

- **The result is conditional.** `cut_expansion` concludes `(h/((d+1)(1+h+(d+1))))·smallSide S ≤ cut R S` only from the caller's `hexpand` (base-graph edge expansion over all `A`), `hR` (R is an involution) and `0 < h`. I checked the arithmetic: B ≤ (d+1)C, E ≤ cut, B ≤ (d+1)·cut, so h·sS ≤ (d+1)(1+(d+1)+h)·cut.
- **Its own docstring lists what stays open:** "Spectral-to-cut and FP instantiation of algFamily remain separate obligations." `table` is described as "computability, not an FP claim". No spectral bound and no polynomial-time claim is made.
- **Representation and boundary.**
  - `graph` builds a `Complexity.RegGraph` with `V = Port n d` and `D = Fin 3`. `graph_degree` and `graph_order` close by `change` to `Fintype.card`, which relies on Complexitylib's `deg` and `order` unfolding that way. Those bodies are not in this packet.
  - `cut` counts each undirected rotation edge once (via /2). Fixed points of `R` contribute 0, and for d+1 ≤ 2 the parallel cycle labels stay distinct.
  - Any spectral-to-cut bridge has to reconcile Complexitylib's expansion and spectral normalisation with this count convention and with the small-side measure in ports versus vertices.

### SamplerParameters (consumed)

- `blocks A h = 2^(2^(A·h²))` and `beta = A·h²/blocks`. I checked `beta ∈ [0,1)`, `mean_rat` (blocks·beta = A·h²) and the zero cases.
- **Size.** The family is doubly exponential in h. Nothing in this packet supports a polynomial-size, encoding or runtime claim for any object indexed by `blocks A h`.
- The docstring is explicit: it "does not discharge proximity, zoom, or fixed-L assembly".
- **Consistency check for integration.** SamplerParameters is pinned consumed while DropTailParameters is not. That is coherent only if the reached constants are the parameter definitions and lemmas, not `actual_tail` or `eventual_actual_tail`.

### TaggedFinite3LinSource (consumed)

- `taggedCopy` is K disjoint tagged copies with the same right-hand sides. It preserves `row_injective`.
- Violations decompose exactly over copies (`taggedCopy_violations`), and a repeated assignment gives exactly `K·violations` (`taggedCopy_repeatAssignment_violations`).
- **Not established:**
  - a theorem that optimal violation fractions are preserved;
  - any gap amplification;
  - any hardness transfer.

## 3. Unconsumed files: what they establish and what they do not

- **Exact finite laws, no premises beyond dimensions:** GaussianRatio, GaussianNearOne (ratio within `leading·(1−error)` and `leading`), TripleRestrictionDimension, TripleRestrictionRank/SubspaceRestriction (unconditional prior codimension failure ≤ (2^c−1)β), GrassmannIncidence, ZoomOutIncidence (exact flag ratios), RobustSourceLineContainment (exceptional transverse mass ≤ 2^−(n−j−d−1)), TaggedQuestionMassBridge (`baseProjection_event_card = K^J·|A|`, tagged bad mass ≤ J(J−1)C/(K·|Row|)) and SubmoduleFunctionalGluing.
- **Conditional and posterior results.** PosteriorDensity, PosteriorReweighting, GoodAdvice, ZoomOutPosterior and ZoomOutTransfer carry explicit premises (good marginal, cutoff tail, fixed W). Every one disclaims posterior independence. Each W-event is bounded for a single W fixed before the draw; nothing is uniform over W or a union over W.
- **Existential thresholds.** `eventual_good_advice`, `eventually_ready`, `eventual_zoom_out`, `eventual_comparison`, `eventual_transfer` and `eventual_joint_success` give a non-effective `∃ N`. No explicit threshold or rate is given beyond the stated `decay` exponents.
- **Disclosed inputs that are not proved:**
  - ZoomOutJoint: "the fixed-score decoder interface is an input, not a decoder existence proof" (`hdecoder`).
  - VectorAdvice: "not a complete prover strategy".
  - RobustSourceLineContainment: "does not assert a robust decoder or any CMMSA consequence".
  - WeightRounding: "does not assert computational hardness or runtime". Its `polynomial_denominator_bound` is a numeric size bound only, and the gap halves (sig → ⌊sig/2⌋).

I re-checked the numerical steps, all of which hold:
- the `Ready` budget (coefficient 4(A+4r+212));
- `ready_advice`, `ready_zoom_scaled` and `ready_density`;
- `dimension_budget`;
- `zeta_div_le_decay20`, `numerical_small` and `total_error_small`;
- `score_threshold` and `ready_posterior_success` (C/8);
- `rounding_budget_transfer` (9σt/16 < σt).

## 4. Findings

| ID | Severity | Declarations | Finding and disposition |
|---|---|---|---|
| P5‑1 | Medium (evidence tier) | All declarations in the 20 unconsumed files, plus any unreached declaration in the 4 consumed files | There is compile evidence only; none of these is among the 173 roots, so none has a fresh axiom profile. **Do not credit** any eventual or advice, zoom-out or rounding theorem as profiled or as material evidence. |
| P5‑2 | Medium (provenance) | 15 "UNCOMPILED / source draft / not compiled" banners, including on consumed MatrixGrassmannIdentity, PortCycleReplacement and SamplerParameters. Also "Author exports passed; independent review pending" (TripleRestrictionRank, SubspaceRestriction), "Root4.13 … accepted separately" (GrassmannIncidence) and "pending author dependency" (ZoomOutTransfer) | These are stale against the pins. They carry no evidential weight in either direction. Remove before render. |
| P5‑3 | Medium (open, disclosed) | `cut_expansion`, `graph`, `table` | Conditional on `hexpand`. Spectral-to-cut, FP/algFamily instantiation and the Complexitylib `RegGraph` semantics are **open** in this packet. |
| P5‑4 | Medium (computational boundary) | `blocks`, `beta`, `dyadicScale`, `table` | The family is doubly exponential, and the results are size bounds only. **No runtime, encoding or polynomial-size claim** is supported. |
| P5‑5 | Medium (open, disclosed) | `ready_joint_success`, `eventual_joint_success` | The decoder (`hdecoder`) is supplied by the caller. Agreement is only handled above C ≥ max(2·2^(−10h²), 16·2^(−30h²)). |
| P5‑6 | Low–Med (material guard) | `grassmann_le_twice_moment`, `alpha_bounds` | The factor 2 needs `hsmall`, and both need `d+w ≤ finrank V`. Integration must confirm which direction the material consumer uses and that it discharges these guards. |
| P5‑7 | Low | `Properties`, `fixed_subspace_failure_transfer`, `ready_fixed_rank_failure` | Bounds are per fixed W only. `Properties`' `Q.val ≤ W` premise is unused. |
| P5‑8 | Low | `posteriorMixture`, `conclusion_mass_defect` | This is a sub-probability: null retained fibres lose mass, with a defect below `qdecay 10 h`. Do not treat it as normalized. |
| P5‑9 | Low (fidelity) | `retained_gaussian_ratio_le` ("Manuscript constant" 4, where 2 is provable), `gaussian_near_one_half_J` ("used in the manuscript's rank-stable posterior"), `gaussian_near_one` (the ratio is near `leading`, not near 1) | Manuscript fidelity is open. The names and docstrings could mislead. |
| P5‑10 | Low (hygiene) | About 13 files lack `autoImplicit false`. MatrixGrassmannIdentity sets `respectTransparency false`. PosteriorDensity raises `maxHeartbeats`. In RobustSourceLineContainment, `W` names an ambient type | Statements only become more general, and the elaboration options do not affect the kernel check. Cosmetic. |
| P5‑11 | Info | TaggedFinite3LinSource | An exact disjoint-copy identity. Preservation of the optimum fraction is not stated, and no amplification is claimed. |
| P5‑12 | Info (trace consistency) | SamplerParameters is consumed while DropTailParameters is not; GrassmannFlagPosterior is consumed while GrassmannIncidence is not | Consistent only if the reached constants avoid those modules. Integration should confirm from the trace. |

## 5. Questions for integration

1. Which constants of PortCycleReplacement, SamplerParameters, TaggedFinite3LinSource and MatrixGrassmannIdentity are actually reached? Which consumer reaches them (FixedPortCycleFamily, the Cmmsa/Tagged families, AnalyticMoment)? Do they enter the material root's statement or hypotheses (`hsel`)?
2. Are all 23 Complexitylib bodies reviewed in other packets? This includes `RegGraph`'s `deg`/`order`/expansion conventions and any ExpanderFamily interface, which must not be assumed by citation. Is there a spectral-to-cut bridge consistent with `cut` and `smallSide` here?
3. Does the material consumer use MatrixGrassmannIdentity only in the matrix ≤ Grassmann direction (`alpha ≤ 1`), and does it discharge `d+w ≤ finrank V` and, if used, `hsmall`?
4. Does the exported `selected_actual_material_moment_bound_original` have exactly the original conclusion and guards, with `hSpectral`, the selector, failed-zoom, strict-rank and positive-parameter premises retained? This is not checkable in this packet.
5. What are the external definitions used here but not supplied: AdviceExceptions, ConditionedCovering (`retainedConditional`, `deletedConditional_eq_advicePosterior_mixture`, `badZoom`), CoveringSpan/CoveringTV, DropTailParameters, MatrixGrassmannFibre (`card_rankArray`, `uniform_extension_law`), `Finite3LinSource` and `rowConflict`, and Formula?

## 6. Safe conditional claim for this packet

Under the pinned kernel and Init/Mathlib/Batteries trust and the qualified native receipts, the following holds:

- **The Grassmann identity.** For every finite F₂-space V with d+w ≤ dim V, every pair of Boolean predicates and every t, the uniform matrix t-copy moment equals α times the uniform Grassmann t-copy experiment. α is the probability of the actual joint rank event and lies in [0,1].
- **The port/cycle replacement** has cut expansion h/((d+1)(d+2+h)) *whenever* the base rotation is an involution with edge expansion h.
- **Tagged copies** add violations exactly.
- **The remaining files** prove finite sampler, posterior, zoom-out and rounding facts under their explicit premises. They have compile evidence only, with no fresh axiom profile.

**Not claimed:**
- Spectral47, expander existence or spectral-to-cut;
- decoder existence or robust8S;
- source hardness or gap amplification;
- any runtime, FP or polynomial-size bound;
- Complexitylib correctness;
- the exactness of the material export;
- manuscript fidelity;
- zero total warnings;
- any whole-manuscript verdict.
