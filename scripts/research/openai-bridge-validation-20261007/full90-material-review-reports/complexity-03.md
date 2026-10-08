# Complexity review, Full90 packet 3 of 5

## Verdict: GO-WITH-NOTES for this packet only

- **Coverage:** all 43 supplied complete bodies were read in full. None was skipped.
- **No reuse:** every one of the 43 is on the `new_or_changed_complete_bodies` list, so no prior review is reused.
- **Soundness:** I found no unsound statement, reversed bound, hidden added premise or arithmetic error.
- **Main caveat:** at the parameters the selector picks, there is no untagged `QuestionCenter`. That makes the selected-parameter theorems over it vacuously true. The full argument is in C1.
- **Scope of the verdict:** it is about these bodies only. It does not accept the material moment bound, the source/star route, numeric-NO, the reduction, runtime, Complexitylib or the manuscript.

**Method.** I used no tools and ran no Lean or Lake. I did not recompute hashes. I take the native evidence as stated: 173 standard root profiles and fixed source identities. Findings are cited by declaration name.

**Not in this packet:**
- **The material root.** The new root `selected_actual_material_moment_bound_original` (in `ActualSelectedComplementHC46OriginalApplication.lean`) is not here. Neither are `original_HC46_exact` and `selected_actual_material_moment_bound`. I cannot check the exported conclusion, the removal of `hHC`, or the remaining `hSpectral`, selector, failed-zoom, strict-rank and positive-parameter premises from this packet. That check stays open for integration.
- **Complexitylib.** None of the 23 Complexitylib context files is in this packet, and no file here imports Complexitylib directly. Its boundary review is not done here. The packet does depend indirectly on `FixedPortCycleFamily.degree` (see C9).

## File coverage (43 of 43 inspected; ✔ = pinned `transitively_consumed: true`)

1. ActualOccurrenceCounts
2. ActualOccurrenceDegree
3. ActualOrdinaryStarMatchingFiber ✔
4. ActualOrdinaryStarSelection
5. ActualOrdinaryStarWeightedSelection ✔
6. ActualPredrawLeafTable
7. ActualPresentedLeafGluing
8. ActualQuestionCenterCollisionBound
9. ActualQuestionCenterDomainDraw
10. ActualQuestionMassBridge
11. ActualRankImageRightBasisInvariance ✔
12. ActualRawRestrictionComposition
13. ActualRhsFunctionalConstruction ✔
14. ActualSelectedSpectralParameters ✔
15. ActualStarAcceptance
16. ActualStarAcceptedGoodMass
17. ActualStarAcceptedRankGoodFiber
18. ActualStarAffineFunctionalSelection
19. ActualStarAffineFunctionalSelectionForce
20. ActualStarAffineFunctionalSelectionForceSelection
21. ActualStarBadMassWitness
22. ActualStarCoordinateExtensionLawBridge
23. ActualStarDomainDrawEventBridge
24. ActualStarDomainDrawTwoIndexEventBridge
25. ActualStarExtensionProduct
26. ActualStarFiniteUnionBound
27. ActualStarFixedCenterFirstMoment
28. ActualStarFixedCenterNumericalClosure
29. ActualStarFixedCenterScalarClosure
30. ActualStarFixedRhoDimensionGuard ✔
31. ActualStarFixedRhoTwoIndexGuard
32. ActualStarJointKernel
33. ActualStarKernelSupport
34. ActualStarLineIncidence
35. ActualStarQuestionSupport ✔
36. ActualStarRelationCount
37. ActualStarSameLawTwoIndexComposition
38. ActualStarSideConditionAgreement
39. ActualStarSpanIntersection ✔
40. ActualStarSupportCatalog
41. ActualTaggedCanonicalNoComparison
42. ActualTaggedComplementIncidence ✔
43. ActualTaggedComplementStarDensityBridge ✔

I found no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `unsafe`.

## What I checked and found correct

**Material-path parameters (`selected_spectral_parameters`)**
- From `bOf m ∣ h` it derives `leafK = 2·(h / bOf m)`, `leafT + leafK = 2h`, and `ρ = leafK / (2h) = 1 / bOf m` exactly.
- It keeps both the existing `base m ≤ h` floor and the new `cutoff(ρ) ≤ h` floor (through `max`), so no earlier selector guard is dropped.
- It states no spectral or moment bound, which matches its header.

**Right-basis invariance**
- Multiplying on the right by any matrix with a two-sided inverse preserves the range and injectivity of every matrix. No rank premise is needed.
- `actualAppendRankImageMoment_actualLeaf_mul_right_eq` keeps the same center draw and the same shared base matrix.

**Weighted functional selection**
- The exact counts are correct: the dual has 2^dim elements, the matching fibre has 2^(dim − (t + m(d−t))) elements, and the center fibre has 2^(dim − t).
- The averaging step is correct: Σ_f (X − cβ) ≥ εM/2 − cB = εM/4 = Σ_f b, so some f satisfies X ≥ cβ + b and X ≤ β.
- `ordinary_good_mass_gt_half` holds: good mass ≥ S minus a bad mass below S/2. Its tables C and T are fixed in advance.

**Star counting and scalar closure**
- The union bound and the cylinder factorisation are both exact.
- The relation count is (|A| − 1)^(|S| − 1).
- The binomial step gives Σ_S y^(|S|−1)·(x/y)^|S| ≤ (1 + x)^m / y = 2^(mk) / (2^N − 1).
- That is below 2^−(E+1) whenever mk + E + 2 ≤ N.
- The empty-support and `d = t` cases are handled without dividing by zero.

**Dimension guard (`fixedRho_ambient_dimension_guard`)**
- The guard reduces to leafT + m·leafK + E + 2 ≤ 2h + 2mh + 2 ≤ 2h² < 2·blocks.
- This needs h ≥ 2m + 3, which follows from h ≥ bOf m.

**Tagged complement law**
- The complement count is 2^(J(2J−t)), and the incidence balance |Comp|·[2J choose t]₂ = |Centers|·2^(J(2J−t)) holds.
- `sideConditionalDensity_eq_ordinaryComplementStarDensity` is an exact reindexing. The tables C and T′ stay globally fixed.
- `actual_implies_ordinary_star_accepts` drops the RHS checks, which only enlarges the ordinary event. That is the right direction for bounding actual acceptance by ordinary acceptance.

**Collision and sizes**
- Pair collision is 1/[2J−t choose 2h−t]₂, which is at most the Gaussian ratio, which is at most 2^−2J under `hexp`. The union over pairs is at most 2^−J when k² ≤ 2^J. The Gaussian monotonicity argument is correct.
- Output size: rows = m + 4·edgeCount ≤ (1 + 18·deg)·m.
- Variable degree is at most 4.
- The ordered-question bad mass is at most 157·J(J−1)/|RowId|, using 1 + 3·4 + 9·16 = 157.

## Findings

| ID | Severity | Declarations | Finding and disposition |
|---|---|---|---|
| **C1** | **HIGH (non-claim / vacuity)** | `selected_restrictionToK_accept_rankGood_pos`, `selected_labelledTransverse_accepts_rankGood`, `selected_transverseStar_*`, `selector_starAcceptsCenter_not_jointlyDirect`, `selected_domainDraw_rankFailure_mass_lt_threshold_twoIndex`, `selected_actual_center_quotient_dimension_guard(_twoIndex)` | Each takes `q : QuestionCenter I (blocks A h) t` over the **untagged** `I : Instance N nRows`, but no such `q` exists at the selected parameters (argued below the table). Every one of these selected-parameter theorems is therefore vacuously true. None of their modules is consumed, but `ActualStarFixedRhoDimensionGuard` is, so per-constant reachability needs checking. They must not be credited as source/star evidence. The tagged route (`taggedSource I copies`) is the only place a question can exist, and it needs `copies` large enough for J rows (see C3). |
| C2 | MEDIUM | `labelledTransverseLaw`, `selected_labelledTransverse_accepts_rankGood`, `restrictionToKAccepts` | Labels are drawn uniformly as part of the sample; they are not fixed prover tables. The positivity witness is the all-zero labelling, which always accepts and has atom mass 1/|Ω|. This says nothing about soundness against a fixed table, and the header's "positive accepted rank-good mass" should be read that way. The valid fixed-table version is `ordinary_good_mass_gt_half`. |
| C3 | MEDIUM (numeric / runtime, cross-packet) | `successMargin`, `badExponent`, `exists_weighted_matching_functional`, `actual_bad_ordered_question_uniform_mass_le` | (a) The scale is S = 2^−E with E = 2·nRows·(h − 1000q), roughly 2·nRows·h. (b) Weighted selection loses a further 2^−m(d−t) = 2^−2mq, with q = h/(4000m²). (c) The ordered-question bound is non-trivial only if \|RowId\| ≫ J², and J is doubly exponential in h. That points to a tagged instance of doubly exponential size, which is a direct question for the encoded-reduction and runtime gates. None of the usefulness questions are settled here; numeric-NO stays open. |
| C4 | MEDIUM (quantified hypothesis) | `selected_spectral_parameters`, `analyticSourceHeightFloor` | The result depends on `hsel`, and on a `cutoff : ℝ → ℕ` and `base` chosen by the caller. Nothing here shows that some L makes the selector return m, so `hsel` might never be satisfiable for a fast-growing Spectral47 cutoff. The size of hBlock is also not bounded. Integration must show `hsel` can be met with the cutoff actually instantiated in the material root. |
| C5 | LOW (evidence scope) | consumption pins | `OrdinaryStarMatchingFiber` and `OrdinaryStarWeightedSelection` are marked consumed, while `ActualStarJointKernel` and `OrdinaryStarSelection` are not. Yet `matchingStar_fibre_card` uses JointKernel, and `ordinary_star_selects_weighted_functional` uses `ordinary_good_mass_gt_half`. So probably only definitions (`MatchesStar`, `matchingStarMass`, `matchingCenterMass`) are reached. The theorems may carry no fresh profile. Credit only the constants the per-constant trace actually lists. The same applies to the consumed `TaggedComplementIncidence` and `ComplementStarDensityBridge`. |
| C6 | LOW (hygiene / warning disposition) | `ActualStarAcceptance`; `QuestionMassBridge`, `QuestionSupport`, `SpanIntersection`; `QuestionMassBridge`; `ActualOccurrenceDegree`; several files | `set_option linter.unusedVariables false` in `ActualStarAcceptance` means "zero owned warnings" partly reflects a disabled linter. In-file `#print axioms` commands in the next three files emit info output into the build log. `QuestionMassBridge` never closes its namespace. `ActualOccurrenceDegree` still carries a stale "Uncompiled source draft" banner. Several files raise `maxHeartbeats` (to 2,000,000 file-wide in two of them). |
| C7 | LOW | `jointPair_equalLeaf_accepted_rankGood`, `selected_transverseStar_starAcceptsCenter_rankGood` | The good event is empty and the inequality is 0 ≥ 0, which is trivial. These are really negative results: Rel-based acceptance can never be rank-good. Do not cite them as acceptance mass. |
| C8 | INFO | `exists_predraw_leaf_table`, `exists_weighted_matching_functional`, `exists_uniform_match_mass_ge`, `drawComplement` | These choices are classical, averaging or existential, and have no computational content. Any decoder or runtime claim needs separate constructions. Choices fixed before the draw are correctly separated from the sample. |
| C9 | INFO (external family) | `edge_count_bound`, `rows_length_le` | The size is linear only if `FixedPortCycleFamily.degree` is a true constant and `representative_count_bound` holds. Both are outside this packet and connect to the expander interface, so they belong to the Complexitylib boundary review. |
| C10 | INFO | `TaggedCanonicalNoComparison` | It correctly states `[Nonempty (TaggedGoodU …)]`, `hexp` and `k² ≤ 2^J` as premises. T′ depends on (C, T) but is fixed before the draw. The 2^−J collision cost is charged explicitly. |

**Why there is no untagged `QuestionCenter` at the selected parameters (C1):**
- A `QuestionCenter` requires `card_U : U.card = J` with `U : Finset I.RowId`.
- `rows_length_le` bounds the row count: |RowId| ≤ (1 + 18·deg)·nRows.
- The in-packet lemma `htower` gives J = blocks A h > 2^(A·h²).
- The selector gives h ≥ nRows + 2 ≥ 258, so J exceeds |RowId|, and no question U of size J exists.
- The only way out is an astronomically large `FixedPortCycleFamily.degree`, which is defined outside this packet.

## Questions for integration
1. **Material root.** Check the exact statement of `selected_actual_material_moment_bound_original`: `hHC` removed, everything else the same, and the same `Tc`, `fc`, `r` and 2e. Check that it does not route through the selected-leaf wrapper. Also check whether its `hsel` cutoff is the same one passed to Spectral47 (C4).
2. **Per-constant trace.** Which constants are reached in the consumed modules here (C5)? Is the vacuous `selected_actual_center_quotient_dimension_guard` among them (C1)?
3. **Tagged instance size.** What value of `copies` and what tagged row count make `TaggedGoodU` inhabited at J = blocks A h? How large is the encoded instance, and what is the reduction's runtime (C1, C3)?
4. **Expander degree.** Complexitylib review: is `FixedPortCycleFamily.degree` really constant, and is the ExpanderFamily interface proved rather than assumed (C9)?
5. **Spectral47 cutoff.** Can `hsel` be met for the Spectral47 cutoff, and how large does hBlock get (C4)?

## Safe conditional claim
Under the pinned trust and the stated native receipts, these 43 modules contain correct finite counting, law-transport and averaging lemmas. Material-relevant pieces, for this packet only:
- the selected parameters satisfy ρ = 1/bOf m exactly, with cutoff(ρ) ≤ h, given `hsel`;
- the rank-image indicator is invariant under invertible right-basis changes;
- with C and T fixed, some functional f satisfies X ≥ (S/4)·2^−m(d−t)·β + (S/4)·2^−(t+m(d−t)), given the guard and the score premise.

All statements about the untagged selected question center are vacuous at the selector's parameters. Labelled-law positivity carries no information about fixed-table soundness.

Still open: the material root's statement and guards, Spectral47, numeric-NO, source/star/robust8S, the reduction, runtime and learning gates, Complexitylib, the disposition of warnings and info output, a fresh checkout, and manuscript fidelity. No whole-manuscript verdict is given.
