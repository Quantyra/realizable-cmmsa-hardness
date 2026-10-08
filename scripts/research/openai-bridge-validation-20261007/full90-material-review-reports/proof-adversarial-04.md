# Packet 4/5 proof-adversarial review: Full90 material consumer

**Verdict for this packet: GO-WITH-NOTES.** This covers only the 36 files in packet 4. It is not material acceptance and not a manuscript verdict.

I read all 36 supplied project bodies in full and skipped none. I found no soundness defect, no vacuous headline statement, no inequality pointing the wrong way, and no added `hHC` premise. The notes cover four things:
- **Evidence scope:** 28 of the 36 modules have no constant on the fresh trace.
- **An open Complexitylib dependency that is on the trace.**
- **Stale provenance text.**
- **Questions that other packets must answer.**

**What this verdict cannot cover:**
- **The material export.** The body of `ActualSelectedComplementHC46OriginalApplication.lean` is not in this packet. I cannot check that `selected_actual_material_moment_bound_original` passes `original_HC46_exact` into the identical material theorem and keeps every other guard.
- **Complexitylib.** None of the 23 Complexitylib context bodies is in this packet.

**Method.** No tools were used, so I did not recompute hashes or run Lean or Lake. Compile status and the profiles of the 173 roots come from your receipts. References are by declaration name.

## Files inspected (36 of 36, 0 skipped)

The "Trace" column is the pinned `transitively_consumed` flag. "Yes" means at least one constant is reached, so the fresh profile covers **only the reached constants**. "No" means compile evidence only, with no axiom profile.

| # | File | Trace | Status |
|---|---|---|---|
| 1 | ActualTaggedComposedPhysicalSampler | no | inspected |
| 2 | ActualTaggedConcreteStarLaw | **yes** | inspected |
| 3 | ActualTaggedConditionalDomainCollision | no | inspected |
| 4 | ActualTaggedConditionalDomainDraw | no | inspected |
| 5 | ActualTaggedFixedCenterGeometry | **yes** | inspected |
| 6 | ActualTaggedFixedTableAcceptance | **yes** | inspected |
| 7 | ActualTaggedFixedUDensityForce | no | inspected |
| 8 | ActualTaggedMZSideDraw | no | inspected |
| 9 | ActualTaggedOrderedClassCollisionBound | no | inspected |
| 10 | ActualTaggedOrderedFullLawForce | no | inspected |
| 11 | ActualTaggedOrderedQuestionSourceBridge | no | inspected |
| 12 | ActualTaggedOrderedSampleNonempty | **yes** | inspected |
| 13 | ActualTaggedPresentationFiberAudit | no | inspected |
| 14 | ActualTaggedPresentedSelection | no | inspected |
| 15 | ActualTaggedQuestionMass | no | inspected |
| 16 | ActualTaggedQuestionRetainedMass | no | inspected |
| 17 | ActualTaggedSelectedDecoderBridge | no | inspected |
| 18 | ActualTaggedTargetPresentationInvariant | no | inspected |
| 19 | ActualTaggedVertexPhysicalAcceptance | no | inspected |
| 20 | ActualTaggedVertexPhysicalLaw | no | inspected |
| 21 | ActualTaggedVertexPresentationFiber | no | inspected |
| 22 | ActualTypedMixedTower | no | inspected |
| 23 | AdviceExceptions | no | inspected |
| 24 | BernoulliMGF | no | inspected |
| 25 | ConditionedCovering | no | inspected |
| 26 | CoveringSpan | **yes** | inspected |
| 27 | CoveringTV | **yes** | inspected |
| 28 | DropCountTail | no | inspected |
| 29 | DropTailParameters | no | inspected |
| 30 | EqualityGadget | **yes** | inspected |
| 31 | ExceptionRepair | no | inspected |
| 32 | ExpanderCutInstantiation | no | inspected |
| 33 | FiniteConcentration | no | inspected |
| 34 | FiniteSampling | no | inspected |
| 35 | FixedPortCycleFamily | **yes** | inspected |
| 36 | Formula | no | inspected |

All 36 are on the new/changed list, so none is reused from prior reviews. No Complexitylib context body was supplied in this packet.

## What I checked and found correct

### Tagged star law and selection (files 1–21)

**Geometry and acceptance**
- `tagged_fixedCenter_le_leafDomain`: the decomposition x = (x − proj x) + proj x is correct.
- `taggedAccepts_global`: an honest assignment passes, using the stored `q.K`.
- Both tables are fixed globally before any draw.

**Dimensions and nonemptiness**
- Coordinate space has dimension 3J (rows in a good question have pairwise disjoint supports), the equation span has dimension J, and the complement has dimension 2J.
- `taggedCenterOver_nonempty` needs t ≤ 2J.
- `taggedLeafOver_nonempty` needs t ≤ 2h ≤ 2J. K is extended inside a complement C that contains it.

**Domain law**
- `taggedDomainDraw_card` = gaussian(2J−t, 2h−t), computed through the quotient by K ⊕ H_U, which has dimension t + J.
- The fibre over each domain is exactly 2^{J(2h−t)} (`tagged_conditional_presentation_fiber_card`, through `card_conditional_complements` with dim C = 2h, dim K = t, dim H = J).
- So a uniform presented leaf pushes forward exactly to a uniform domain (`uniform_taggedLeafDomain_pushforward`, `composedDomainLaw_mass`). This is a pointwise atom identity.

**Presentation and vertex counts**
- Each vertex has 2^{J·2h} presentations (`vertexPresentation_card`).
- U is determined by the domain (`tagged_goodU_eq_of_equationSpan_eq`).
- Uniform class representatives push forward to uniform full vertices.
- Physical acceptance depends only on the vertex. Transport is source-coherent by uniqueness of the glued RHS functional.

**Selection inequality** (`tagged_physical_mean_le_selected_mean_add_collision`, `tagged_exists_selected_mass_ge_physical_sub_collision`)
- On distinct classes: physical ≤ validified = selected, using injective-key restriction of the uniform product law.
- Otherwise the collision indicator pays the 1.
- The selected choice s is fixed before the draw, and the weights only need to be ≥ 0.

**Ordered law**
- Each fibre has J! elements, so the pushforward is exactly uniform `TaggedGoodU`.
- The dependent-kernel pushforward shows `orderedStarLaw = taggedSampleLaw`.
- Padding: bad mass ≤ J(J−1)·157 / (K·rows) ≤ 1/T, good mass ≥ 3/4 when T ≥ 4, and the good set has positive cardinality.

**Collision bound** (`taggedSampleClassCollisionMass_le_twoNegJ`)
- With the same U, class equality is the same as domain equality, because H is shared.
- The pair collision probability is exactly 1/#domains.
- The ratio bound is 1/G ≤ 2^{−(2h−t)(2J−2h)}, which is ≤ 2^{−2J} under `hexp`, and C(k,2)·2^{−2J} ≤ 2^{−J} under k² ≤ 2^J.
- The guards force J = 0 when h = J.

**Density forcing**
- The disintegration over U is exact.
- If E[δ] ≥ β and δ ∈ [0,1], then P(δ ≥ β/2) ≥ β/2.
- Threshold arithmetic: 2^{−J} + 16·2^{−p} ≤ 2^{−(q+1)} whenever q + 6 ≤ p ≤ J.
- p − q = 6000ρhm.

**Composition and MZ side draw**
- `composedTaggedScore_eq_orderedPhysicalMass` is exact.
- `taggedAccepts_iff_sideAccepts` / `conditionalCanonicalDensity_eq_side` are exact changes of variables. Uniform mass is preserved and there is no reweighting.
- No MZ decoder conclusion is claimed.

### Probability and covering (files 23–29, 31, 33, 34, 36)

**Concentration and tails**
- `BernoulliMGF`: Hoeffding's lemma via curvature. The key step is (1−p+pe^t)² ≥ 4(1−p)pe^t.
- `FiniteConcentration`: the Markov step uses t = 4δ, giving exp(−2Mδ²) per tail. There are 2^N assignments, and the ε/8 + ε/8 split is correct.
- `DropCountTail`: the product moment comes from `prior` itself, not from an assumed independence. The Chernoff bound (eμ/T)^T is correct, including μ = 0 (the T = 0 case uses the 0⁰ convention).
- `DropTailParameters`: h⁴ ≥ 100h², the base is ≤ 1/2, and decay100/decay30 = decay70. This is conditional on the exact equality `hmean`.

**Covering**
- `CoveringTV`:
  - E[B²] = (N² + 2N)/3, so the χ² term is β²(E[B²] − 1) ≤ β²N².
  - The Hellinger bound is ≤ χ², tensorization costs a factor J, and TV ≤ √H² under the unhalved-H convention.
  - The block mixture matches the retained-coordinate law ("some k" keeps only coordinate k).
- `CoveringSpan`:
  - The span kernel pushes a uniform array to the uniform Grassmannian exactly.
  - Correction = (1−f)·subspaceLaw + f·uniform.
  - Triangle bound: β√J·2^a + βJ(2^a−1)/2^J ≤ β√J·2^{a+4}, using J/2^J ≤ √J.
- `ConditionedCovering`:
  - The per-fibre identity is p_Y(post_p − post_q) = (pK − qK) + (q_Y − p_Y)·post_q, which gives an average ≤ 2·TV.
  - Markov at zoomError·2^{d+5} is correct, including the zero-error branch.
  - Requiring β < 1 (derived from 2^dβ ≤ 1/8) makes every conditioning event positive.
- `AdviceExceptions`: the event-mass bound ≤ TV, the low-marginal mass ≤ 2TV, and the Markov tail all go in the correct direction. Null marginals contribute 0.

**Exception repair**
- `ExceptionRepair` / `Formula`:
  - λε ≤ s/2, so the total cost is ≤ 3σs/8.
  - avg(e) ≤ 3γ/8, so the repaired average < γ + 3γ/8 < 2γ.
  - Completeness is exact, and there is exactly one extra leaf per formula.
- `FiniteSampling`: the cumulative rounding error is < 1/D, mass error ≤ 1/D, event error ≤ S/D, and the dyadic precision gives ε/8. The list sampler is exactly uniform.

### Gadget and expander (files 30, 32, 35)

**EqualityGadget**
- The four rows sum to x + y, so the violation count is at least the mismatch.
- The extension a = c = e = 0, b = x, d = y attains it.
- Degrees are 1/1/2 and pairwise intersections are ≤ 1.
- These were all checked by `decide` over the 2⁷ assignments, and I agree with them by hand.

**ExpanderCutInstantiation**
- Half the dart crossings equal the outgoing darts, by the involutive rotation.
- |S||Sᶜ|/n ≥ min/2.
- The empty graph is handled.
- These are correct **given** the Complexitylib lemma statements (see PA4-02).

**FixedPortCycleFamily**
- `finCongr` relabelling preserves numeric dart values (`baseRotation_values` by `rfl`).
- The replacement graph has degree 3 and n·degree vertices.
- The cut coefficient κ > 0 does not depend on n.
- There is no FP/runtime claim, and the docstrings say so.

## Findings

| ID | Severity | Declarations | Finding and disposition |
|---|---|---|---|
| PA4-01 | Medium (evidence scope) | All 28 modules marked "no" above; partial reach inside the 8 "yes" modules | Most theorems here have **no fresh axiom profile**: the selection comparison, collision bound, MZ forcing, composed-value bridge, Hoeffding, Chernoff, the advice and conditioned covering results, exception repair and the expander cut. They are also **not on the material trace**. The flags pin down which declarations are unreached even inside consumed modules:<br>• `ActualTaggedPresentedSelection` is unconsumed, so `TaggedLeafOver`-dependent declarations (for example `taggedLeafOver_nonempty`, `paddedOrderedStarLaw`, `tagged_sample_exists_selected`) are unreached.<br>• `AdviceExceptions`/`PosteriorDensity` are unconsumed, so `actual_advice_tv_le(_manuscript)` and `rationalTV_cast` are unreached.<br>• `ExpanderCutInstantiation` is unconsumed, so `kappa`, `cut_expansion`, `boundary_expansion` and `boundary_eq_cut` are unreached.<br>**Disposition:** credit them as compiled source only, and never as profiled or as material-path evidence. |
| PA4-02 | Medium (open boundary, on the trace) | `FixedPortCycleFamily.degree/base/baseRotation/graph/table`; `Complexity.algFamily`, `RegGraph.relabel/ofRot/spectralBound_relabel`, `card_dartsBetween_compl_ge`, `sum_darts_boundary` | The reached constants refer to the concrete `Complexity.algFamily`. It is a constant, not an assumed `ExpanderFamily` hypothesis, and no polynomial-time claim is made. But its value and fields are **not reviewed here**, and if it carries proof fields, reaching `.graph` pulls its whole spectral proof closure (ExpanderExists/Random, PermCount, ZigZag, TowerFin, FamilyFin, ExpanderPad) into the trust base. The fields in question are `degree`, `lam`, `lam_lt_one`, `spectral_graph`, and V = Fin n for **every** n, which relies on padding. The exact meaning of `SpectralBound` (normalized? one- or two-sided?) and the statement of `card_dartsBetween_compl_ge` are also open. **Disposition:** OPEN, and must be covered by the Complexitylib packets. |
| PA4-03 | Low–Medium (provenance) | Banners in AdviceExceptions, CoveringTV, CoveringSpan, ConditionedCovering, DropCountTail, DropTailParameters, ExpanderCutInstantiation, **FixedPortCycleFamily (on trace)** | Their "UNCOMPILED" / "SOURCE DRAFT" banners contradict the 319-closure receipt. Some docstrings also say work is open or unproved when another file proves it:<br>• CoveringTV header: says the span bridge is "OPEN"; CoveringSpan proves it.<br>• `exceptional_chernoff_bound`: says TV is "undisclosed"; `actual_adviceTV_le_manuscript` proves it.<br>• `ordered_manuscript_half_value…`: says the transfer is "unproved"; `composedTaggedScore_eq_orderedPhysicalMass` proves it.<br>• ConcreteStarLaw header: says the marginal and collision results are still to do; OrderedQuestionSourceBridge and ClassCollisionBound prove them.<br>• ConditionalDomainCollision header: advertises a collision mass the file does not contain.<br>**Disposition:** no evidential weight either way; fix before render. |
| PA4-04 | Low | `ExceptionRepair`, `Formula` | `#print axioms` sits inside non-Checks library modules. That output was not supplied and is not evidence. It produces build-log info lines. |
| PA4-05 | Low | ActualTaggedQuestionMass and ActualTaggedQuestionRetainedMass reopen namespace `ActualQuestionMassBridge` | For example, `ActualQuestionMassBridge.actualPaddingCopies` is defined outside `ActualQuestionMassBridge.lean`. Trace and module attribution must use the declaring module, not the namespace. |
| PA4-06 | Low (fidelity) | `ordered_manuscript_half_value_forces_MZ_threshold_U`, `composedScore_gt_forces_MZ_threshold_U`, `composedLegalValue_gt_forces_*`, `…side_threshold_U` | In `hp`/`hq`, `m` is the `Instance N m` index. ξ, ρ and m are used only to derive q + 6 ≤ p. The constants 1000, 4000 and 6000, and what m means, are not checked against the manuscript. The p and q natural-number equalities are caller obligations. |
| PA4-07 | Low | `composedLegalValue`, `TaggedLegalRawTable` | The maximum is taken over fully legal raw tables only (illegal tables score 0). This is not a soundness gap, because `composedScore_gt_forces_MZ_threshold_U` holds for arbitrary T. But the manuscript-value bridge "unrestricted value > Δ implies legal value > Δ" (true by monotonicity) is not stated. Integration should cite the arbitrary-T theorem. |
| PA4-08 | Info (modelling) | `TaggedLeafOver`, `taggedPhysicalAccepts`, `taggedAccepts` | Three modelling choices need manuscript confirmation:<br>• The center is stored inside L, the transverse increment. This is proved equivalent in law to uniform domains.<br>• The physical verifier reads a uniform full-vertex representative of the queried class and transports by RHS-preserving gluing.<br>• With k = 0 leaves, acceptance is vacuous. |
| PA4-09 | Info | `ActualTypedMixedTower` | This module has only the tower definitions and `length_le_total_finrank`. No tower A15 bound is proved, and nothing consumes it. |
| PA4-10 | Info | BernoulliMGF (`convert!`, `try simp only`), several `maxHeartbeats` raises | These are elaboration fragility only; the kernel still checks every proof. |

## Questions for integration or other packets

1. **The material export (OriginalApplication, another packet).** Confirm that `selected_actual_material_moment_bound_original` is literally `selected_actual_material_moment_bound` with `hHC := original_HC46_exact` and nothing else changed:
   - the same `Tc`, `fc`, `r`, `k`, and η = 2e;
   - `hSpectral : Spectral47ExactContract`, the selector `hsel`, the failed-zoom premise `hfail`, the strict-rank premise and the positive-parameter premises all retained;
   - the conclusion identical;
   - no use of the selected-leaf wrapper.
2. **Do the material statement's guards (for example `hsel` / `analyticSourceHeightFloor`) mention tagged constants from this packet** (`TaggedGoodU`, `TaggedCenterOver`, `questionOf`, the dimensions in `ActualTaggedOrderedSampleNonempty`)? If they do, the meaning of `GoodQuestion` and of "transverse center" carries weight for statement fidelity.
3. **External lemmas these proofs depend on, to be checked in their own packets:**
   - Span intersection and RHS functionals: `equationSpan_inf_coordinateSpace`, `equationSpan_inf_sup_coordinateSpace_le`, `equationSpan_finrank_eq_card`, `existsUnique_rhsFunctional`, `sideCondition_agree_on_intersection`, `existsUnique_glue_on_sup`.
   - Collision and counting: `card_conditional_complements`, `tagged_class_eq_iff_domain_eq_sameU`, `tagged_physical_le_canonical_plus_collision`, `gaussian_small_over_large_le`, `choose_mul_twoNegTwoJ_le_twoNegJ`.
   - Bad-question mass: `conflict_degree_le` (the 157), `tagged_bad_ordered_question_count(_mul_rowCard)_le`.
   - Posterior and incidence: `PosteriorReweighting.total_probability`, `bayes_mass`, `posterior_normalized`, `eventPosterior_eq_conditional`, `containmentProbability_formula`, `upperCount_ratio`, `lowerCount`.
   - Grassmannian and frames: `card_grass_mul`, `frameEquiv`.
   - Cut expansion: `PortCycleReplacement.cut_expansion`, `count_complement`.
4. **Complexitylib (PA4-02):** the complete review of the 23 modules, the construction of `algFamily` (existence and padding to every n), and the RegGraph and spectral API semantics.
5. **Manuscript fidelity:** the KMS 4.7 constants √β·J^{1/4}·2^{d+5}, the tagged padding T ≥ 4, and the ρ/ξ/p/q bookkeeping.

## Safe conditional claim for this packet

Under pinned Init/Mathlib/Batteries trust and the native compile receipt:
- the 36 modules compile and contain the exact identities and inequalities verified above;
- only the reached constants of the 8 consumed modules carry the fresh standard-axiom evidence.

Nothing in this packet adds an `hHC` premise. Nothing here establishes any of the following:
- the material export or its guards;
- Spectral47 or numeric NO;
- the MZ decoder conclusion, source/star/robust8S, or encoded runtime;
- the correctness of the Complexitylib expander family;
- manuscript fidelity.

All of those, and the inherited warning debt, remain open.
