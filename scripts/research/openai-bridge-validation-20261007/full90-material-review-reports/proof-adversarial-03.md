# Proof-adversarial review, Full90 packet 3 of 5

**Verdict for this packet: GO-WITH-NOTES.** This covers packet 3 only. It is not a material-readiness verdict and not a whole-manuscript verdict, and it does not accept anything.

I found no soundness, vacuity, quantifier or direction defect in the 43 supplied bodies. None of the notes block this packet. Several material and source claims built on these files rely on bodies that the fresh trace probably does not reach, so they carry compile evidence only (finding P3-1).

**How I reviewed:**
- I used no tools, made no writes, did not run Lean or Lake, and used no subagents.
- I did not recompute any hash. Whether tactics succeed and the module-level identities rest on the qualified native receipts.
- I cite declarations by name, not line number.
- None of these 43 files is among the 169 bodies eligible for reuse. All are new or changed, so every one got a fresh review here.
- No Complexitylib source is in this packet. The Complexitylib boundary review stays open for integration.

## Coverage: 43 supplied, 43 inspected, 0 skipped

"Consumed" is the `transitively_consumed` pin.

| Consumed = **true** (9) | Consumed = false (34) |
|---|---|
| ActualSelectedSpectralParameters | ActualOccurrenceCounts, ActualOccurrenceDegree |
| ActualRankImageRightBasisInvariance | ActualOrdinaryStarSelection, ActualPredrawLeafTable |
| ActualOrdinaryStarWeightedSelection | ActualPresentedLeafGluing, ActualQuestionCenterCollisionBound |
| ActualOrdinaryStarMatchingFiber | ActualQuestionCenterDomainDraw, ActualQuestionMassBridge |
| ActualStarFixedRhoDimensionGuard | ActualRawRestrictionComposition, ActualStarAcceptance |
| ActualStarQuestionSupport | ActualStarAcceptedGoodMass, ActualStarAcceptedRankGoodFiber |
| ActualStarSpanIntersection | ActualStarAffineFunctionalSelection, …Force, …ForceSelection |
| ActualRhsFunctionalConstruction | ActualStarBadMassWitness, ActualStarCoordinateExtensionLawBridge |
| ActualTaggedComplementIncidence | ActualStarDomainDrawEventBridge, …TwoIndexEventBridge |
| ActualTaggedComplementStarDensityBridge | ActualStarExtensionProduct, …FiniteUnionBound, …FixedCenterFirstMoment, …FixedCenterNumericalClosure, …FixedCenterScalarClosure |
| | ActualStarFixedRhoTwoIndexGuard, ActualStarJointKernel, ActualStarKernelSupport, ActualStarLineIncidence, ActualStarRelationCount, ActualStarSameLawTwoIndexComposition, ActualStarSideConditionAgreement, ActualStarSupportCatalog |
| | ActualTaggedCanonicalNoComparison |

The 10 entries in the left column account for the 9 consumed modules. I read every body in both columns.

In the supplied text I found no `sorry`, `admit`, `axiom` declaration, `native_decide`, `implemented_by`, `unsafe` or `opaque`.

## Checks on the consumed (material-facing) bodies

**ActualSelectedSpectralParameters**
- `leafK_eq_two_mul_quotient` gives leafK = 2q with q = h / bOf m. `leaf_split_total` gives c + s = 2h.
- `selected_spectral_parameters` derives everything from `hsel` alone: 256 ≤ m, m + 2 ≤ h, bOf m ∣ h, 0 < s, the real identities c = 2(1−ρ)h and s = 2ρh, and `base m ≤ h`.
- The rho used is the actual one: ρ = s/(2h) = 1/bOf m, checked via h = b·q.
- The cutoff is evaluated at that exact ρ, not at a bound or surrogate: `cutoff (actualSelectedRho …) ≤ h`.
- The selector-spec positions (component 6 = divisibility, component 8 = floor) match the positions used in AcceptedGoodMass.

**ActualRankImageRightBasisInvariance**
- For any U, V with UV = VU = 1, range(MU) = range(M) and the two maps are injective together. No rank premise is needed, so rank-deficient M is covered.
- This gives exact invariance of `rankImageBoolean`, of the center and leaf indicators, of `appendAverage`, and of `actualAppendRankImageMoment`. The center draw and the shared base stay identical.
- This is the right-basis-invariance input that Spectral47 needs. It is stated for the same `leafMatchBit T f`, not a surrogate.

**ActualOrdinaryStarWeightedSelection and ActualOrdinaryStarMatchingFiber**
- `matchingStarMass` and `matchingCenterMass` are event masses under `starLaw` for a fixed f.
- Fibre count: f = base + ψ∘mkQ, and the glued ψ needs the full-family direct-sum injectivity (`jointlyDirect`), not pairwise conditions. The count is 2^{n−(t+m(d−t))}.
- Double-count averaging: Σ_f(X_f − cβ_f) ≥ (ε/2)M − (ε/4)M = (ε/4)M = Σ_f b, with b = (ε/4)(M/F), F = 2ⁿ and |Dual| = 2ⁿ by `dual_card`. Both directions check, and X ≤ β.
- `ordinary_good_mass_gt_half`: good ≥ accepted − bad > S − S/2. The inequality is strict because bad < S/2.

**ActualStarFixedRhoDimensionGuard**
- leafT + m·leafK + badExp + 2 ≤ 2h + 2mh + 2 ≤ 2h² < 2·blocks.
- The middle step needs h ≥ 2m + 3. That follows from h ≥ bOf m ≥ 3m together with m ≥ 256.

**ActualStarQuestionSupport, ActualStarSpanIntersection, ActualRhsFunctionalConstruction**
- `new_row_private_coordinate` holds: rows have 3 points and overlap the support in at most 1.
- span(U′) ∩ coord(U) = span(U′ ∩ U): evaluating at the private coordinate forces the coefficient to 0.
- The equation vectors are independent, so the RHS functional exists and is unique, and the equation span has dimension |U|.

**ActualTaggedComplementIncidence**
- The number of complements of H containing a fixed K is 2^{J(2J−t)}.
- That gives the balance |Comp|·[2J choose t]₂ = |Centers|·2^{J(2J−t)}, and each observed (K, D⃗) atom is reweighted exactly.
- The ordinary leaf L ⊂ A and the full domain D correspond one-to-one via D = H ⊔ L and L = A ⊓ D (modular law). The dimension 2h checks.
- The chain side density = observed full density = complement full density = ordinary A-first star density consists of equalities only.

**ActualTaggedComplementStarDensityBridge**
- The center and leaf tables are pullbacks of the one predrawn pair (C, T′) along each complement's inclusion. They are deterministic in A and do not depend on the star draw.
- `actual_implies_ordinary_star_accepts` gives pointwise: actual tagged acceptance ⇒ ordinary `StarAccepts`, with the RHS checks dropped. That is the correct direction for an upper bound on NO acceptance.
- Both domain identifications (`transported_center_domain_eq`, `transported_leaf_domain_eq`) are exact.

**Unconsumed bodies.** The fixed-center first-moment chain checks out:
- `kernelWitness_has_exact_support_relation` gives support ≥ 2.
- The relation count is ≤ (|A|−1)^{|S|−1}.
- The cylinder masses factor exactly.
- The support sum is ≤ 2^{mk}/(2^N−1), which is < 2^{−E−1} when N ≥ mk + E + 2.
- The two-index transport goes through the preimage equivalence.

Other checks that pass:
- Collision bound: 1/[2J−t choose 2h−t]₂ ≤ the Gaussian ratio ≤ 2^{−2J}, then C(k,2) ≤ k² ≤ 2^J. I recomputed the identity behind `normalizedFrame_relative_mono` as p(M−A)(C−1)/(AMC) ≥ 0.
- QuestionMassBridge: 1 + 3·4 + 9·16 = 157.
- OccurrenceCounts: 4E ≤ 18·deg·m.
- `agreementExponent_lt_badExponent`: holds because b = 4000m² ≥ 1008.

## Findings

| ID | Severity | Declarations | Finding | Disposition |
|---|---|---|---|---|
| P3-1 | Medium (integration, material/source) | `exists_weighted_matching_functional`, `ordinary_star_selects_weighted_functional`, `matchingStarMass_sum_ge_good`, `sideConditionalDensity_eq_ordinaryComplementStarDensity`, `actual_implies_ordinary_star_accepts` | **These sound proofs link NO-instance acceptance to a fixed f, but they almost certainly sit outside the fresh trace.** They depend on modules pinned unconsumed: ActualFiniteIncidenceSampling (`eventMass_uniform_eq_card`), ActualStarAcceptedGoodMass, ActualOrdinaryStarSelection, and ActualTaggedMZSideDraw (`SideCenter`, `sideAccepts`, `sideConditionalDensity`). So in the consumed modules probably only definitions are reached: `MatchesStar`, `matchingStarMass`, `SideComplement`, the transported tables. That is an inference, not an enumeration. | Credit as compile-only. The material theorem quantifies over the given f, and the link from acceptance to f stays OPEN under the source/star gates. Per-constant enumeration needed. |
| P3-2 | Low (non-claim) | `jointPair_equalLeaf_accepted_rankGood`, `selected_transverseStar_equalLeaf_accepted_rankGood`, `selected_transverseStar_starAcceptsCenter_rankGood`, `selector_starAcceptsCenter_not_jointlyDirect`, `selected_restrictionToK_accept_rankGood_pos` | **These "accepted rank-good" results carry no NO or YES soundness content.** In the first three, the accepted-and-good event is empty and r is chosen as the acceptance mass itself, so they are trivial. The fourth proves that `starAcceptsCenter`/`LeafVertex.Rel` acceptance can never coexist with rank-good. The fifth gets its positivity from uniformly random labels via the all-zero atom, not from fixed predrawn tables. | Never cite as acceptance evidence. |
| P3-3 | Low (docs) | ActualOccurrenceDegree header ("Uncompiled source draft"); ActualPredrawLeafTable header and docstring | The "uncompiled" banner is stale. The PredrawLeafTable header claims the table "extends by zero on its transverse summand", but `exists_predraw_leaf_table` picks T by `Classical.nonempty_pi`; the zero extension only witnesses nonemptiness. The theorem itself (RHS agreement) holds for any LeafLabel. | Fix before render. |
| P3-4 | Info | ActualStarQuestionSupport (3×), ActualStarSpanIntersection (1×), ActualQuestionMassBridge (1×) | Embedded `#print axioms` commands produce build info output, and the first two modules are consumed. Their output was not supplied. | Include in the warning and info disposition. |
| P3-5 | Info | ActualStarAcceptance `set_option linter.unusedVariables false`; raised `maxHeartbeats` in several files | A linter is suppressed, so "zero owned warnings" partly reflects suppression. The heartbeat changes affect elaboration only. | Note for the warning gate. |
| P3-6 | Info | ActualQuestionMassBridge | The final `end` closes only the section, leaving the namespace open at end of file. Local `{X E}` binders shadow the section variables. | Hygiene. |
| P3-7 | Info (integration) | ActualOccurrenceCounts and ActualOccurrenceDegree; `Instance` fields | These rely on `FixedPortCycleFamily.degree`, `ActualGraphEdges.representative_count_bound` and Instance fields (`sum_sizes`, `pair_intersection`, `recover_anchor`), all in other packets. | Confirm whether Instance or FixedPortCycleFamily pulls Complexitylib ExpanderFamily in as an assumed interface or as a proved one. |

## Questions retained for integration
1. Per-constant trace membership for the 9 consumed modules here. In particular, are only definitions reached, and is any theorem from P3-1 reached?
2. The exact `material_moment_bound_original` export (not in this packet). Does it instantiate Spectral47 with `cutoff` equal to the `analyticSourceHeightFloor` cutoff from `hsel`, with `basisInv` discharged through `actualLeafIndicator_mul_right_eq` on the same Tc, fc and `hsplit`?
3. Where are `accepts`, `goodStar`, `goodStarMass`, `acceptanceMass` and `StarAccepts` defined (presumably ActualSourceStarLaw or ChangedAmbient8S), and do they match the restriction-to-K test?
4. ActualComplementCoordinateMassBridge: does it turn the ordinary A-star with transported tables into the coordinate tables and functional on Fin n → ZMod 2 without a surrogate?
5. Complexitylib reach through ActualGraphEdges and FixedPortCycleFamily, plus the 23-module boundary review (none of it is in this packet).
6. Pinned Init/Mathlib/Batteries trust is assumed here and was not reviewed.

## Safe conditional claim
Assume the qualified native receipts and pinned library trust. Then:
- The consumed bodies in this packet correctly prove the selected spectral parameters at the exact ρ = 1/bOf m with c + s = 2h, and exact right-basis invariance of the leaf and center rank-image indicators and the append moment.
- They correctly define the matching star and center masses for a fixed functional, and the ordinary-complement transport of one predrawn table pair.
- The unconsumed bodies compile and, on my reading, prove the tagged-to-ordinary acceptance comparison, the incidence reweighting, the weighted functional selection and the fixed-center bad-mass bound. They have no fresh axiom profile.

**Not claimed:** material acceptance; Spectral47; useful numeric NO; source, star or robust8S closure; reduction, runtime or learning; Complexitylib review; zero total warnings; manuscript fidelity; or any full-scope verdict.
