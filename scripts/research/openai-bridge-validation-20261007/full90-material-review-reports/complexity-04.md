# Complexity review, packet 4 of 5: tagged sampler, covering, concentration, gadget and expander-cut files

**Verdict for this packet only: GO-WITH-NOTES.** I read all 36 complete files and skipped none. I found no soundness defect, no inequality pointing the wrong way, no exponent error and no vacuous main result. The notes concern how the results are stated, assumptions that are made but not used, where the Complexitylib boundary sits, and stale header comments.

The overall material review is still **INCOMPLETE**. This packet does not contain the export `selected_actual_material_moment_bound_original`, its module `…HC46OriginalApplication`, or any of the 23 Complexitylib source files. So this packet cannot confirm the exact exported conclusion and its guards, and it cannot be used to review Complexitylib.

How I reviewed: I read the supplied text only. I used no tools, ran no Lean or Lake, wrote nothing and did not recompute any SHA. Compilation and axiom facts come from your receipts. References are by declaration name, not line number.

## Reuse status

None of the 36 files is on the "unchanged prior complete bodies" list. All are in `new_or_changed_complete_bodies`, so every file below is a fresh review and no prior report was reused.

## Files and inspection status

The "consumed" column is the `transitively_consumed` flag from the source pins. Only constants that a root reaches are covered by the fresh standard-axiom evidence. Modules marked "no" have compile evidence only.

| # | File | Consumed | Status |
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

None of these files contains `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` or `opaque`.

## What I re-derived

**Counts and laws**
- **Center-span count** (`taggedDomainDraw_card`). The coordinate space has dimension 3J, the center span t+J, the quotient 2J−t. A domain of dimension J+2h is then counted by the Gaussian binomial G(2J−t, 2h−t). It needs t ≤ 2h ≤ 2J, and the natural-number subtractions are safe under those guards.
- **Fibre of presentations over a domain with the center held fixed.** The count is 2^{J(2h−t)}: these are complements of H (dimension J) containing a K of dimension t, counted as graphs of maps on C/K. Unconditioned, the count is 2^{J·2h} (`vertexPresentation_card`).
- **Pushforwards to uniform laws.** Because every fibre has the same size, the following pushforwards are exactly uniform and no reweighting enters:
  - leaves to domains (`uniform_taggedLeafDomain_pushforward`);
  - leaf tuples (`uniform_leafTuple_pushforward`);
  - representatives to vertices (`uniform_classRepresentative_pushforward`, `uniform_independentChoice_pushforward`);
  - ordered tuples to sets, with J! orderings per set (`orderedGood_pushforward`).

  `composedDomainLaw_mass` is a pointwise identity: uniform U × uniform K × uniform tuple of domains.

**Collision and selection**
- **Class-collision bound.** Each pair collides with probability exactly 1/G. The union bound gives C(k,2)/G. Using G ≥ 2^{(2h−t)(2J−2h)}, then `hexp`, then k² ≤ 2^J, this is at most 2^{−J}. The bound does not depend on the adversarial tables.
- **Representative selection** (`tagged_exists_selected_mass_ge_physical_sub_collision`). The center table C and the raw vertex table T are fixed before the draw. The representative choice s is a function of the tables only, and the canonical table T′ = `taggedSelectedDomainTable T s` is also fixed before the draw. For distinct classes the joint law is exact, and the physical event is at most the validified event.
- **Density thresholds.**
  - `high_density_mass` holds: δ ≤ β/2 + 𝟙[δ ≥ β/2].
  - The half-value step holds: 2^{−J} + 16·2^{−p} ≤ (17/64)·2^{−q} ≤ 2^{−(q+1)} when q+6 ≤ p ≤ J.
  - The manuscript gap is p − q = 6000ρhm ≥ 6.

**Concentration, covering and repair**
- **Concentration and tails.**
  - Hoeffding's lemma holds by the curvature argument (Z² ≥ 4p(1−p)e^t).
  - Choosing t = 4δ gives the tail bound exp(−2Mδ²), and a union bound covers all 2^N assignments.
  - The dropped-block count has an exact product moment. The Chernoff bound (eμ/T)^T applies to the strict tail; the cases T = 0, β = 0 and J = 0 are handled.
  - `Ready` gives a base of at most 1/2 and an exponent of h⁴ ≥ 100h².
- **Covering.**
  - χ² = β²((N²+2N)/3 − 1) ≤ β²N², then Hellinger ≤ χ², tensorization, and TV² ≤ H².
  - The span-kernel pushforward and the rank correction combine through J/2^J ≤ √J to give TV ≤ β√J·2^{a+4}.
  - ConditionedCovering: the average conditional TV is at most 2·TV, and Markov's inequality then gives exceptional mass ≤ √β·J^{1/4}.
- **Exceptional advice and repair.**
  - Exceptional-advice mass ≤ tail/ζ + 3·TV.
  - ExceptionRepair soundness: λ·avg(e) ≤ 3σs/8 forces avg(e) ≤ 3γ/8, so the repaired average is below 2γ.
  - FiniteSampling event error ≤ S/D ≤ ε/8.

**Equality gadget.** Adding all four rows gives x + y, so all rows can be satisfied only if x = y. The extension a=c=e=0, b=x, d=y attains violations equal to the mismatch. The degrees and pairwise intersections stated in the file are correct.

**Same tables throughout.** One fixed C and one arbitrary raw T are used in every identity in the chain:
`composedTaggedScore_eq_orderedPhysicalMass` → `ordered_physical_le_canonical_plus_collision` → `taggedAccepts_iff_sideAccepts`.

## Findings

| ID | Sev. | Declarations | Finding and disposition |
|---|---|---|---|
| C4‑1 | Medium (fidelity) | `ordered_manuscript_half_value_forces_MZ_threshold_U`, `composedScore_gt_forces_MZ_threshold_U`, `composedLegalValue_gt_forces_MZ_threshold_U`, `composedLegalValue_gt_forces_side_threshold_U` | The exponent premises `hp`, `hq` and `hlarge` use `m`. That `m` is the section variable bound by `I : Instance N m`, not a free manuscript parameter. These premises also require 2(1−1000ρ)hm and 2(1−4000ρ)hm to be natural numbers. **Retained:** the numeric and manuscript gates must confirm that the manuscript's m is the instance m, and that integral p and q exist. |
| C4‑2 | Medium (fidelity) | `composedLegalValue`, `TaggedLegalRawTable` | The "value" is a maximum over *legal* raw tables only. No theorem shows that the maximum over arbitrary tables is at most this. Validification is monotone, so such a bridge looks provable, but it is absent. **Mitigation:** the score-level force theorem already holds for an arbitrary T. **Retained:** use the arbitrary-T statement, or match the manuscript's definition of value. |
| C4‑3 | Medium (integration) | All force and selection theorems; `actual_tagged_good_mass_ge_three_quarters`, `…conditioning_factor_le_four_thirds` | Every sampler statement is conditioned on eligible good U. The bad-question mass ≤ 1/T and the conditioning factor < 2 are proved separately. No theorem here bridges the unconditional ordered verifier to the conditioned law. **Open** (source/star lane). |
| C4‑4 | Medium (Complexitylib boundary) | `ExpanderCutInstantiation.*`, `FixedPortCycleFamily.*` | These files use the Complexitylib API: `RegGraph.card_dartsBetween_compl_ge`, `sum_darts_boundary`, `ofRot`/`deg_ofRot`, `relabel`/`spectralBound_relabel`, `rot_involutive`, and `algFamily.{degree, degree_pos, lam, lam_nonneg, lam_lt_one, spectral_graph, graph, rot}`. None of those bodies is in this packet, so I credit nothing from them.<br>ExpanderCutInstantiation is unconsumed while FixedPortCycleFamily is consumed. I infer from this that `kappa`, `cut_expansion`, `boundary_expansion`, `boundary_eq_cut`, and Cheeger's mixing lemma are **not** on the native trace, and only the structural constants (`degree`, `labels`, `base`, `graph`, `table`, …) are reached. That is consistent with Cheeger not being a direct boundary module.<br>So graph expansion is not established on the trace. Neither is the claim that `algFamily` holds for every n (including n = 0, 1, 2) with a uniform λ < 1, nor any explicit or polynomial-time rotation map: the file is `noncomputable`, and its header disclaims any FP claim. **Open:** this goes to the Complexitylib packet and the reduction/runtime gate. |
| C4‑5 | Low (provenance) | Banners on AdviceExceptions, ConditionedCovering, **CoveringSpan**, **CoveringTV**, DropCountTail, DropTailParameters, ExpanderCutInstantiation, **FixedPortCycleFamily** ("UNCOMPILED"/"SOURCE DRAFT"); docstrings of ConcreteStarLaw ("still require separate proofs"), `ordered_manuscript_half_value…` ("separate, unproved" transfer, now proved in ComposedPhysicalSampler), CoveringTV ("span bridge remains OPEN", now in CoveringSpan) | Out of date; they carry no weight as evidence either way. The bold files are consumed while their banner says they are uncompiled. **Clean up before rendering.** |
| C4‑6 | Low | `#print axioms` in ExceptionRepair and Formula | These print info output into the build log, and that output was not supplied. Both modules are unconsumed, so this matters only for the warning/log-disposition gate. |
| C4‑7 | Info | Guards `ht`, `hh`, `hexp`, `hk`, `hpJ`, `hT : 4 ≤ T`, `hm : 0 < m` | Each guard can be satisfied (e.g. t=0, h=⌈J/2⌉, J ≥ 2). `hexp` fails at h = J. All guards must be discharged by the numeric gate. |
| C4‑8 | Info | ActualTaggedQuestionMass and RetainedMass | Both reopen the namespace `ActualQuestionMassBridge`, which belongs to another file. The symbol `T` is overloaded: padding count, raw table, and leaf base elsewhere. A hygiene issue only. |
| C4‑9 | Info | ConditionedCovering `had : a < d` (only a ≤ d is used); FiniteSampling `mass_sum` (needs `cumulative p S = 1`); raised `maxHeartbeats`/`maxRecDepth` | These only add slack or affect the elaborator. Not a soundness issue. |
| C4‑10 | Info | ActualTypedMixedTower | Only the inductive structure and the length ≤ dim D + dim C bound. No A15 bound is stated; the module is unconsumed and nothing is credited. |
| C4‑11 | Info (trace consistency) | Consumed vs. unconsumed pairs | Several consumed modules import unconsumed ones:<br>• OrderedSampleNonempty is consumed; its import OrderedQuestionSourceBridge is not.<br>• CoveringSpan and CoveringTV are consumed; AdviceExceptions, DropCountTail and GrassmannIncidence are not.<br>This is consistent only if the reached constants are the generic ones (frames and finrank lemmas). **Integration should enumerate the reached constants.** |

## Questions for integration

1. Which constants from the 8 consumed modules does the 173-root trace actually reach, and through which consumer? Candidates are AnalyticMoment's Tagged/Cmmsa/OrdinaryStar imports and ActualBinaryGrassmannSamplingBounds. Also confirm that none of them enters the type of the material export.
2. Statements in other packets that this packet relies on: `card_conditional_complements`, `tagged_class_eq_iff_domain_eq_sameU`, `gaussian_small_over_large_le`, `choose_mul_twoNegTwoJ_le_twoNegJ`, `conflict_degree_le` (the constant 157), `TripleRestrictionRank.blockMass` (β/3 for each singleton), `GrassmannFlagPosterior.*`, and `PortCycleReplacement.cut_expansion`.
3. For the Complexitylib packet: the SpectralBound convention, how `algFamily` is constructed (explicit, or a `Classical.choose` from ExpanderExists/ZigZagBaseExists), whether the family exists for every n, and the statement of `card_dartsBetween_compl_ge`.
4. The resolutions to C4‑1 through C4‑3.

## What can safely be claimed

Under the pinned trust in the kernel, Init, Mathlib and Batteries, and the compile receipts. Standard axiom profiles apply only to reached constants; the unconsumed modules have compile evidence only.

- For every center table C and arbitrary raw vertex table T, both fixed before the draw, and under the guards (t ≤ 2h, h ≤ J, `hexp`, k² ≤ 2^J): the ordered tagged physical mass is at most the acceptance of one canonical table, fixed before the draw, plus 2^{−J}.
- Under the exponent premises, a composed score above 2^{−q} forces the MZ side-conditioned density to be at least 8·2^{−p} on at least 8·2^{−p} of the eligible U.
- The supporting results hold as stated:
  - TV ≤ β√J·2^{a+4} and the KMS 4.7 conditioned covering;
  - the exceptional-advice and Chernoff/Hoeffding bounds;
  - exception repair;
  - the exact minimum of the equality gadget.

**Not claimed:**
- the MZ decoder conclusion, NO-soundness, or useful numeric parameters;
- the bridge from the unconditional verifier to the conditioned law;
- graph expansion on the trace, or any computable or polynomial-time expander;
- Complexitylib review;
- the material export's conclusion;
- Spectral47, manuscript fidelity, or any acceptance.
