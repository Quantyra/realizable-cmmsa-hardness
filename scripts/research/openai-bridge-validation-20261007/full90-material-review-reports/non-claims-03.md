# Non-claims review: Full90 material-consumer packet 3 of 5

## Verdict: GO-WITH-NOTES, for this packet only

All 43 files in this packet were read in full. No body was skipped, and I found no blocking defect.

This is not a verdict on material readiness, the exported material theorem, or the manuscript. The body of the material export (`ActualSelectedComplementHC46OriginalApplication.lean`) is not in this packet. So I could not check its exact conclusion and guards here, and I did not substitute any lemma from this packet for it.

**How I reviewed.** I read source text only: no tools, no hash recomputation, no Lean or Lake. The native facts (seven exits at 0, 173 roots, 319 pins, the trace) come from what you supplied. As established earlier, fresh axiom evidence covers only the 173 roots and the constants they reach. Compiling a module does not give every declaration in it a standard profile. I cite by declaration name because line numbers are unavailable.

**Reuse status.** All 43 files are on the new-or-changed list, so none of them gets prior-review reuse. Every body here is a fresh review.

**Complexitylib.** None of the 23 Complexitylib context files is in this packet, and none of these 43 files imports Complexitylib directly. Two of them depend on the expander/port-cycle boundary indirectly, through `FixedPortCycleFamily.degree` and `ActualGraphEdges.representative_count_bound`:
- `ActualOccurrenceCounts`
- `ActualOccurrenceDegree`

That boundary stays open (questions Q5 and Q7). Neither module is on the material trace.

## Files: 43 supplied, 43 inspected, 0 skipped

| # | File | Pinned consumed? | Status |
|---|---|---|---|
| 1 | ActualOccurrenceCounts | no | inspected |
| 2 | ActualOccurrenceDegree | no | inspected |
| 3 | ActualOrdinaryStarMatchingFiber | **yes** | inspected |
| 4 | ActualOrdinaryStarSelection | no | inspected |
| 5 | ActualOrdinaryStarWeightedSelection | **yes** | inspected |
| 6 | ActualPredrawLeafTable | no | inspected |
| 7 | ActualPresentedLeafGluing | no | inspected |
| 8 | ActualQuestionCenterCollisionBound | no | inspected |
| 9 | ActualQuestionCenterDomainDraw | no | inspected |
| 10 | ActualQuestionMassBridge | no | inspected |
| 11 | ActualRankImageRightBasisInvariance | **yes** | inspected |
| 12 | ActualRawRestrictionComposition | no | inspected |
| 13 | ActualRhsFunctionalConstruction | **yes** | inspected |
| 14 | ActualSelectedSpectralParameters | **yes** | inspected |
| 15 | ActualStarAcceptance | no | inspected |
| 16 | ActualStarAcceptedGoodMass | no | inspected |
| 17 | ActualStarAcceptedRankGoodFiber | no | inspected |
| 18 | ActualStarAffineFunctionalSelection | no | inspected |
| 19 | ActualStarAffineFunctionalSelectionForce | no | inspected |
| 20 | ActualStarAffineFunctionalSelectionForceSelection | no | inspected |
| 21 | ActualStarBadMassWitness | no | inspected |
| 22 | ActualStarCoordinateExtensionLawBridge | no | inspected |
| 23 | ActualStarDomainDrawEventBridge | no | inspected |
| 24 | ActualStarDomainDrawTwoIndexEventBridge | no | inspected |
| 25 | ActualStarExtensionProduct | no | inspected |
| 26 | ActualStarFiniteUnionBound | no | inspected |
| 27 | ActualStarFixedCenterFirstMoment | no | inspected |
| 28 | ActualStarFixedCenterNumericalClosure | no | inspected |
| 29 | ActualStarFixedCenterScalarClosure | no | inspected |
| 30 | ActualStarFixedRhoDimensionGuard | **yes** | inspected |
| 31 | ActualStarFixedRhoTwoIndexGuard | no | inspected |
| 32 | ActualStarJointKernel | no | inspected |
| 33 | ActualStarKernelSupport | no | inspected |
| 34 | ActualStarLineIncidence | no | inspected |
| 35 | ActualStarQuestionSupport | **yes** | inspected |
| 36 | ActualStarRelationCount | no | inspected |
| 37 | ActualStarSameLawTwoIndexComposition | no | inspected |
| 38 | ActualStarSideConditionAgreement | no | inspected |
| 39 | ActualStarSpanIntersection | **yes** | inspected |
| 40 | ActualStarSupportCatalog | no | inspected |
| 41 | ActualTaggedCanonicalNoComparison | no | inspected |
| 42 | ActualTaggedComplementIncidence | **yes** | inspected |
| 43 | ActualTaggedComplementStarDensityBridge | **yes** | inspected |

None of these files contains `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` or `opaque`. Only the 10 modules marked "yes" can carry fresh evidence, and only for the specific constants the roots reach. The other 33 modules are compiled but carry no axiom profile.

## Checks on the consumed modules

**`ActualSelectedSpectralParameters`**
- `selected_spectral_parameters` holds only under `hsel`, which says the selector returns some `m`. Given that, it derives:
  - `256 ≤ m`, `m+2 ≤ h`, `bOf m ∣ h`;
  - the split `leafT + leafK = 2h`;
  - `actualSelectedRho = leafK/(2h) = 1/bOf m`. I checked this: `leafK = 2(h/b)`, so ρ = 1/b exactly.
- The cutoff is evaluated at that actual ρ, not at a stand-in value. That cutoff is a function the caller passes in. The file does not prove that it is the Spectral47 source cutoff, nor that the selector returns a value for that cutoff (Q1).

**`ActualRankImageRightBasisInvariance`**
- `rankImageBoolean_mul_right_eq` holds for every matrix, including rank-deficient ones. It assumes a two-sided inverse (`U*V=1`, `V*U=1`).
- The append-average and moment versions apply the same `U` to every leaf lift. The center and the shared base are unchanged.

**`ActualOrdinaryStarMatchingFiber` and `ActualOrdinaryStarWeightedSelection`**
- Fibre count (`matchingStar_fibre_card`): exactly 2^(n−(t+m(d−t))), assuming acceptance and joint directness.
- Averaging step (`exists_weighted_matching_functional`). I checked it with:
  - c·B = εM/4 and Σb = εM/4;
  - ΣX ≥ εM/2.
- The step is lossy: the coefficients are εM/(4B) = ε·2^(−m(d−t))/4 and εM/(4F).

**`ActualTaggedComplementIncidence`**
- The identity `sideConditionalDensity = ordinaryComplementStarDensity` is exact. It rests on the incidence balance:
  - complement count × gaussian(2J, t) = center count × 2^(J(2J−t));
  - this goes through `side_complements_over_card`, which needs `ht` and `hh`.

**`ActualTaggedComplementStarDensityBridge`**
- `actual_implies_ordinary_star_accepts` is a pointwise implication from the actual test to the ordinary test.
- The direction is correct: actual density ≤ ordinary density on the transported tables.

**`ActualStarFixedRhoDimensionGuard`, `ActualStarQuestionSupport`, `ActualStarSpanIntersection`, `ActualRhsFunctionalConstruction`**
- These hold arithmetic and linear algebra only.
- I checked `equationSpan_inf_coordinateSpace` and the independence and uniqueness of the RHS functional. Independence uses only pairwise-disjoint rows.

## Checks on the modules not consumed

**Fixed-center bad-mass chain** (JointKernel, KernelSupport, BadMassWitness, SupportCatalog, ExtensionProduct, FirstMoment, NumericalClosure, ScalarClosure):
- The bad event is failure of joint directness for the whole family. It is not replaced by a pairwise test.
- The candidate catalog is fixed before sampling.
- I checked the scalar bound:
  - Σ_S x^|S|/y = (1+x)^m/y = 2^(mk)/(2^N−1);
  - with N ≥ mk+E+2, this is < 2^(−E−1).

**`starLaw_bad_mass_lt_threshold`** is a genuine average of the fixed-center bounds over the center. The fibres are equal-sized, so ΣU|fibre| = |Ω|.

**DomainDraw bridges** (CoordinateExtensionLawBridge, DomainDrawEventBridge, TwoIndex bridge, SameLawTwoIndexComposition):
- Every docstring says the uniform DomainDraw law is not the manuscript's physical sampler. That statement is accurate.
- The arity premise `r ≤ nRows` is an explicit hypothesis, not something the file derives.

**`ActualQuestionCenterCollisionBound`**
- The chain is: pair collision = 1/gaussian(2J−t, 2h−t), which is ≤ the clique ratio, which is ≤ 2^(−2J). The last step needs `hexp`.
- Over all pairs the bound is ≤ C(k,2)·2^(−2J) ≤ 2^(−J), which needs `k² ≤ 2^J`.
- Both `hexp` and `k² ≤ 2^J` are assumed, not discharged.

## Findings

| ID | Severity | Declarations | Finding | Disposition |
|---|---|---|---|---|
| N1 | **Medium** (overclaim risk) | `selected_restrictionToK_accept_rankGood_pos`, `selected_labelledTransverse_accepts_rankGood`, `labelledTransverseLaw` | The "acceptance" event draws the center and leaf labels uniformly inside the same experiment. Positivity is witnessed trivially by all-zero labels (`w0`). The inequality is just the generic union bound with r = bad mass. Nothing here bounds acceptance for a fixed table, or for any prover. | Not reached by any root. Never cite as soundness or acceptance evidence. |
| N2 | **Medium** (obstruction) | `selected_transverseStar_equalLeaf_accepted_rankGood`, `selected_transverseStar_starAcceptsCenter_rankGood`, `selector_starAcceptsCenter_not_jointlyDirect` | The accepted rank-good event in these lemmas is empty (mass 0). Acceptance tests built on `LeafVertex.Rel` / `starAcceptsCenter` can never be rank-good at two leaves. | Keep as a proved negative result. Acceptance based on `Rel` (`ActualStarAcceptance`) cannot carry a good-mass argument. |
| N3 | **Medium** (material vacuity, cross-packet) | `selected_spectral_parameters`, `analyticSourceHeightFloor` | Every guard depends on `hsel`. Nothing here shows the selector returns a value when its floor includes the true Spectral47 cutoff evaluated at ρ = 1/(4000m²) with m ≥ 256. If `hsel` can never hold, the material export is vacuous. | Open (Q1). |
| N4 | **Medium** (numeric usefulness) | `actual_good_ordered_question_uniform_mass_ge`, `actualCliqueCollisionMass_le_twoNegJ`, `exists_weighted_matching_functional`, `selected_extensionCount_gt_halfMargin` | Each bound has content only under a parameter condition: the ordered-question mass needs \|RowId\| > 157·J(J−1); the collision bound needs `hexp` and `k² ≤ 2^J`. The weighted selection loses a factor of 2^(−m(d−t)), and `blocks A h` is tower-sized. | Numeric NO and runtime remain open. |
| N5 | Low | `ActualOccurrenceDegree` header | The header says "Uncompiled source draft". That is stale, since the file is in the pinned closure. Being compiled still does not mean it is profiled (not consumed). | Fix before render. |
| N6 | Low | `#print axioms` in ordinary source files: QuestionSupport (×3), SpanIntersection, QuestionMassBridge (`conflict_degree_le`) | These commands write output into the build log. That output is not campaign axiom evidence. | Fold into the log disposition and do not credit it. |
| N7 | Low | `ActualStarAcceptance`: `set_option linter.unusedVariables false`; file-level `maxHeartbeats 2000000` (AcceptedGoodMass, StarDensityBridge) and local raises | "Zero owned warnings" is partly achieved by suppressing the unused-variable linter. The heartbeat raises affect elaboration only. | Note for the warning disposition. |
| N8 | Low | `ActualStarAcceptedRankGoodFiber`, `actualCliqueCollisionMass`, `exists_predraw_leaf_table` | Names promise more than the code delivers: (1) the "AcceptedRankGoodFiber" module only proves RHS agreement and a carrier identity; (2) the "actual" collision mass is taken under the uniform DomainDraw law; (3) the "predraw" table is an honest table, extended by zero, and says nothing about adversarial tables. The docstrings mostly disclaim this. | No weight beyond what is literally proved. |
| N9 | Info | Pinned consumption flags | Several modules are marked consumed while their selection theorems' dependencies are not (AffineFunctionalSelection, OrdinaryStarSelection and AcceptedGoodMass are all unconsumed). This suggests only definitions such as `matchingStarMass` and `MatchesStar` are reached. Why the Tagged incidence, density-bridge and RHS modules are consumed cannot be determined from these bodies. | Enumerate reached constants (Q2). |
| N10 | Info | `actual_implies_ordinary_star_accepts` | Transported tables are fixed functions of (C, T′, A), but they change with the complement A. Closing the bound needs ordinary-star soundness for all tables, of the `AllAmbientInverse` type, and that is unproved. | robust8S / source-star stays open. |
| N11 | Info | QuestionMassBridge namespace left open at end of file; `h` shadowing in `starAccepts_of_source_agrees`; plain `/- -/` comment before `set_option … in def` (Force); `rowConflict` is reflexive by design (the count includes `e` itself) | Cosmetic. | — |
| N12 | Info | `ActualRawRestrictionComposition` | The nominal budget is additive, and the fibre is exactly the intersection. This is consistent with nominal-budget semantics. | — |

## Questions for integration (across packets)

1. **Q1.** Is there a proof that `selector (fun j => max (analyticSourceHeightFloor base cutoff j) (j+2)) L` returns a value for the instantiated Spectral47 cutoff? Is that cutoff exactly the one quantified in `Spectral47ExactContract`? (N3)
2. **Q2.** Which constants from the 10 consumed modules are actually reached? In particular:
   - confirm that neither `ordinary_star_selects_weighted_functional` nor any AcceptedGoodMass lemma is reached;
   - explain why the Tagged incidence and bridge modules are marked consumed.
3. **Q3.** Does the material export state exactly `selected_actual_material_moment_bound` with `hHC := original_HC46_exact`, and keep `hSpectral`, `hsel`, `hfail`, the strict rank guard and the positive-parameter premises? This needs checking in the packet that holds its body.
4. **Q4.** Does Spectral47's invariance premise (`basisInv`) have the two-sided-inverse form that `actualLeafIndicator_mul_right_eq` requires, or the `IsUnit det` form? (N12-adjacent)
5. **Q5.** Complexitylib and expander boundary: `FixedPortCycleFamily.degree`, `representative_count_bound` and `sum_sizes` feed `edge_count_bound` and `rows_length_le`. Review them in the packets that hold them.
6. **Q6.** Instantiate \|RowId\| against J: is 157·J(J−1) < \|RowId\| ever satisfied, given that J = `blocks A h` is tower-sized? (N4)
7. **Q7.** Is `AllAmbientInverse`, or any universal ordinary-star soundness bound, proved anywhere? (N10)

## Safe conditional claim for this packet

Assuming the qualified native receipts and the pinned kernel and library trust, these 43 bodies prove the following finite facts, each under the hypotheses stated with it:
- the fixed-center bound on full-joint-directness failure, and its average under `starLaw`;
- exact fibre and incidence counts;
- the exact identity between tagged conditional density and ordinary complement star density;
- the pointwise implication from actual to ordinary acceptance;
- invariance of the rank-image indicator under invertible right-basis changes;
- the selected-parameter identity ρ = 1/bOf m (given `hsel`).

**Not claimed:**
- any acceptance or soundness bound for a fixed table or prover (N1, N2);
- that the selector returns a value for the true cutoff;
- usefulness of the numeric NO parameters;
- that any DomainDraw or uniform law is the physical sampler;
- Spectral47, source/star/robust8S, the reduction, runtime or learning;
- review of the Complexitylib bodies;
- the exported material conclusion;
- standard profiles for unreached declarations;
- zero total warnings;
- any verdict on the manuscript as a whole.
