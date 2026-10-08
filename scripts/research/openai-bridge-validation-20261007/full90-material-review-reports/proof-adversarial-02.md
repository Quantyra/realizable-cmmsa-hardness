# Packet 2 of 5: proof-adversarial review of the Full90 material consumer

## Verdict: GO-WITH-NOTES (this packet only)

This packet contained 42 complete files. I read every one and skipped none. I found no soundness, vacuity, quantifier or proof-direction defect in any of them.

This verdict does not cover material readiness. It is not acceptance and not a manuscript verdict. I ran no tools, no Lean/Lake, made no writes and recomputed no hashes. Source identity rests on the supplied pins, and kernel acceptance rests on the native receipts.

**What this packet cannot settle:**
- **Exported conclusion and guards.** The body of `selected_actual_material_moment_bound_original` (in `ActualSelectedComplementHC46OriginalApplication.lean`) is not here. So I can't check its exact conclusion, its guards, or that only `hHC` was removed. That check stays with integration.
- **Complexitylib.** None of the 23 Complexitylib bodies are in this packet. The Complexitylib boundary obligation is still open.

## File coverage (42 inspected, 0 skipped)

| # | File | Status | On the 173-root path? |
|---|---|---|---|
| 1 | A12InfluenceBoundChecks | inspected (harness only) | no |
| 2 | A20SquareGlobalnessChecks | inspected (harness) | no |
| 3 | A21DyadicMomentChecks | inspected (harness) | no |
| 4 | A8AmbientAssemblyChecks | inspected (harness) | no |
| 5 | A8AveragedAssemblyChecks | inspected (harness) | no |
| 6 | A8AveragedTransportChecks | inspected (harness) | no |
| 7 | A8EndpointChecks | inspected (harness) | no |
| 8 | A8EnergyNaturalityChecks | inspected (harness) | no |
| 9 | A8PairAssemblyChecks | inspected (harness) | no |
| 10 | A9ActualFiber | inspected | no (prior trace: 0 reached constants) |
| 11 | HC46CommonDerivative | inspected | no (0 reached constants) |
| 12 | HC46FinitePeeling | inspected | no (0 reached constants) |
| 13 | HC46MixedPeeling | inspected | no (0 reached constants) |
| 14 | ActualCliqueCollisionTransfer | inspected | no |
| 15 | ActualCliqueJointLaw | inspected | no |
| 16 | ActualCliqueScoreTransfer | inspected | no |
| 17 | ActualCmmsaAdmissibilitySelector | inspected | **yes** |
| 18 | ActualCmmsaParameterReconciliation | inspected | **yes** |
| 19 | ActualCompatibleRhsFunctional | inspected | no |
| 20 | ActualComplementCoordinateMassBridge | inspected | **yes** |
| 21 | ActualEqualityCloud | inspected | **yes** |
| 22 | ActualEqualityCloudDegree | inspected | no |
| 23 | ActualFinite3LinSource | inspected | **yes** |
| 24 | ActualFiniteIncidenceSampling | inspected | no |
| 25 | ActualFiniteLaw | inspected | **yes** |
| 26 | ActualFiniteMomentLpBounds | inspected | **yes** |
| 27 | ActualFixedFunctionalAppendOperator | inspected | **yes** |
| 28 | ActualFixedFunctionalBinaryMatrixMoment | inspected | **yes** |
| 29 | ActualGraphEdges | inspected | **yes** |
| 30 | ActualGraphIncidence | inspected | no |
| 31–37 | ActualLeafCenterRestriction, LeafPresentationDescent, LeafRejectionUnion, LeafRelationLaws, LeafRepresentativeSampler, LeafTransport, LeafTransportCoherence | inspected | no |
| 38 | ActualMZ24ComplementRestriction | inspected | no |
| 39 | ActualMZ24DistinctPairAggregation | inspected | no |
| 40 | ActualMZ24FixedZoomListBound | inspected | no |
| 41 | ActualMZ24GenericSubfamilyRepresentative | inspected | no |
| 42 | ActualOccurrenceAllocation | inspected | **yes** |

"Yes" means the pin marks the file `transitively_consumed: true`. Only the declarations that roots actually reach carry fresh axiom evidence. Files marked "no" compile but have no axiom profile, and I give them no credit. That includes every declaration in the nine `*Checks` harnesses, since the harness outputs themselves were not supplied. The roots those harnesses name do appear in the fresh 173-root stdout with standard axioms; `a21_exponent_le` and `a21_density_recurrence` use only subsets of the standard three.

In the supplied text I found no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `opaque` or `unsafe`.

## What checks out on the material path

**ActualFiniteMomentLpBounds** (all over unconditional uniform carriers; no rank-conditioned law and no added premise):
- `appendAverage_abs_pow_le`: Jensen is applied in the right direction. |mean F| ≤ mean |F|, then (mean)^p ≤ mean(·^p) with weights N⁻¹.
- `appendAverage_lpMoment_le`: the two-stage uniform draw equals the full uniform draw. The card factorisation goes through `appendBinaryMatrixEquiv`.
- `lpNorm_add_le`: Minkowski on raw sums, then (x/N)^{1/p} = x^{1/p}/N^{1/p}.
- `finite_sum_lpNorm_le`: the empty case gives 0^{1/p} = 0 with p ≥ 1.
- `finiteLevel_sum_abs_pow_le`: the bound is card^{p−1}. The edge case of an empty family with p = 1 works because 0^0 = 1 times 0 is 0.

**ActualFixedFunctionalAppendOperator / ActualFixedFunctionalBinaryMatrixMoment:**
- `finSumFinEquiv` keeps the base columns first. The appended range equals the span of `concatenate M B`, including when columns are dependent, and injectivity is equivalent to linear independence of the concatenation.
- `rawG` and `rawF` agree with `rankImageBoolean` for every array. Rank-deficient matrices score 0 on both sides.
- The same `Rset`/`Lset` are used at every draw, and one base matrix is shared across all k extensions.
- `matchingStarMass ≤ 2·actualAppendRankImageMoment` is conditional on `hD`, `hsmall` and the external `grassmann_le_twice_moment`. The direction is correct.

**ActualComplementCoordinateMassBridge:**
- The basis equivalence `A.1 ≃ₗ Fin(2J) → 𝔽₂` transports the Grassmannian, the extensions, the star tuples, the tables and the functional `f ∘ e⁻¹`.
- The pushforward of the uniform star law is uniform, by `pushforward_uniformLaw_equiv`. This relies on `starLaw` unfolding to `uniformLaw`, which a `change` step checks.
- The matching and center events correspond exactly in both directions, via `cancel_right` on a surjection. Both mass identities are equalities.

**ActualFiniteLaw:**
- `eventSub ≤ TV`: 2Σ_E(μ−ν) ≤ Σ|μ−ν| + Σ(μ−ν) = Σ|μ−ν|.
- Pushforward composition holds, TV contracts under pushforward and is invariant under equivalences, and agreement equals the uniform event mass.

**ActualCmmsaParameterReconciliation:**
- `hn_handoff` is correct: 8·(g/16) = g/2, and (g/2)^{m+1}·g^{−(m+1)} = 2^{−(m+1)} ≤ 1/2 ≤ 5/8.
- `amplified_leaf_fit_of_hBlock` is correct: R ≤ blockNum = ⌊(L−1)/d⌋ gives d·R + 1 ≤ L.
- `old_sigma_route_failure` is conditional on gap < R.

**ActualCmmsaAdmissibilitySelector:**
- The selector is `WithBot`, so an empty admissible set gives ⊥ rather than a default value.
- `selector_spec` returns admissibility, including 256 ≤ m, together with maximality.
- `admissible_eventually` holds for every `sourceHMin`. The witness is L ≥ 2^K, giving T ≤ log₂ blockNum, then H ≤ hBlock, then 4m ≤ hBlock. That yields an exponent ≥ 7, so gap ≥ 128 and σ ≥ 8.
- The source threshold stays an explicit parameter and is not manufactured anywhere.

**Occurrence, equality-cloud, graph and 3LIN files** (they enter the material statement through the type of `I`):
- Anchors are injective via `recover`, distinct rows intersect in at most 1 variable, and `rows_mem_iff` holds in both directions.
- The cloud's exact minimum is attained simultaneously at every port.
- Representative darts select exactly one dart per orbit, and the crossing count equals the actual cut, with multiplicities.

**Peeling files (11–13; correct but uncredited):** The loss recursion exponent closes: 2 + 4(r+k+1) + 4rk + 2k² + 4k = 4r(k+1) + 2(k+1)² + 4(k+1). In the mixed case, 4lk + 2l² + 2k² = 2(k+l)². Rank-zero annihilation follows from rank = drop + 1 on selected frequencies.

**Off-path files:**
- Johnson bound in FixedZoomListBound: via centered one-hot features, N·|Ω|·c ≤ √(N|Ω|)·√|Ω|, so N ≤ 1/c².
- 16/β² list bound: from β/2 ≥ 2^{−b} + β/4 when β > 4/2^b, with full-rank mass ≥ 1/2 when 10d ≤ dim W.
- Clique selection: the averaging argument gives `selectedScore ≥ originalScore − collisionMass`.
- Leaf gluing: the private-coordinate argument (each excluded question overlaps the row in at most 1 of its 3 variables) gives linear independence over three good questions. Transport is unique, coherent and independent of presentation.

## Findings (none blocking)

| ID | Severity | Declaration | Disposition |
|---|---|---|---|
| P2-1 | Medium (integration) | export body (not supplied) | The exact exported conclusion, its guards, and that `hSpectral`, the selector, failed-zoom, strict-rank and positive-parameter premises remain while only `hHC` is removed, cannot be checked here. Retained. |
| P2-2 | Medium (boundary) | `ActualGraphEdges.crossing_card_eq_cut`, `crossing_expansion`, `outgoing_eq_actual_darts` | These use `Complexity.RegGraph.dartsBetween`, `ExpanderCutInstantiation.*` and `FixedPortCycleFamily.kappa`/`cut_expansion`. Graph expansion is **not** established by this packet. The Complexitylib bodies and any assumed ExpanderFamily interface still need review. The material type also depends on `I` and therefore on this graph family. |
| P2-3 | Medium (integration) | `matchingStarMass_cast_le_twice_actual*` | Conditional on `MatrixGrassmannIdentity.grassmann_le_twice_moment` and `hsmall` (other packet) and on `matchingStarMass_cast_eq_grassmannExperiment` (prior review). |
| P2-4 | Low (integration) | `hn_handoff` | It needs `16 ∣ gapRoot`, `0 < gapRoot` and the ζ bound. `Admissible` implies the exponent is ≥ 7, so these hold, but no packaged lemma here proves it. Confirm the consumer discharges them. |
| P2-5 | Low (warning disposition) | `ActualLeafRejectionUnion` | Sets `linter.unusedVariables false`. Zero owned warnings is partly achieved by suppression here. |
| P2-6 | Low (provenance) | `ActualEqualityCloudDegree` header | Says "Uncompiled source draft", which is stale. The file is pinned but not consumed. |
| P2-7 | Low | `ActualComplementCoordinateMassBridge` | Uses `respectTransparency false`, raises heartbeats, and declares a local `Fintype` instance on `StarTuple`. These affect elaboration only, but downstream statements may hit instance mismatches. |
| P2-8 | Info (manuscript) | `E1_47` / `E1_not_75` (and the 127/150, 216/225 pairs) | The formal geometric output exponent ⌊100c²hD⁵/(c+1)⌋ − 3c disagrees with the 75/150/225 values these lemmas rule out. This is a fidelity item and not consumed. |
| P2-9 | Info | `A9ActualFiber` | Its B0 convention is the opposite of the ambient A9 fiber, and the header says ambient transport is separate. Do not credit it. |
| P2-10 | Info | `ActualFiniteIncidenceSampling.mean_mul_tv_sq_le_one` | Correct but loose: the proof yields 1/4. Not consumed. |
| P2-11 | Info | `ActualMZ24FixedZoomListBound` | Has an unused `hinj` and large commented-out failed proof drafts. No effect on soundness. |
| P2-12 | Info (numeric-NO) | `admissible_eventually` | L₀ is existential and not explicit, and `tD` is astronomically large. Usefulness is not shown. |

## Questions for integration

1. Exact type of `selected_actual_material_moment_bound_original`: does it apply the identical original theorem with `hHC := original_HC46_exact`, with no surrogate and no selected-leaf wrapper?
2. Which `FixedPortCycleFamily`, `ExpanderCutInstantiation` and Complexitylib constants are reached, and whether any `ExpanderFamily` hypothesis is assumed rather than proved.
3. The `MatrixGrassmannIdentity`, `GaussianRatio`, `ActualTaggedComplementIncidence` (`sideComplement_finrank`), `ActualPresentedLeafGluing`, `ActualStarSideConditionAgreement` and `ActualOccurrenceCounts` bodies, which are in other packets.
4. Disposition of P2-4, P2-5 and P2-8.

## Safe conditional claim

Assume the native receipts and pinned library trust, and treat every external lemma named above as an open cross-packet dependency. Then for the reached constants of files 17, 18, 20, 21, 23, 25–29 and 42, the following holds:
- The unconditional append/moment Lp bounds hold.
- The fixed-functional star mass is at most 2× the explicit actual append-column rank-image moment, using a shared base and the same tables. This is conditional on `hsmall`, `hD` and the Grassmann identity.
- Coordinate transport of the selected side complement preserves both masses exactly.
- The CMMSA selector is honest about an empty admissible set and is eventually populated for any fixed source threshold.

No claim is made on any of the following: the material moment or its export guards, Spectral47, numeric-NO, graph expansion, Complexitylib, source/star/robust8S, reduction, runtime or learning, upstream items, warnings, fresh checkout, the manuscript, or the final providers.
