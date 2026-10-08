# Complexity review, Full90 packet 2 of 5

## Verdict: GO-WITH-NOTES, for this packet only

I read all 42 supplied files in full and skipped none. I found no soundness, vacuity, quantifier, direction or exponent defect.

This verdict does not cover the following:
- **Material review is not complete.** The explicit root `selected_actual_material_moment_bound_original`, the `MatrixGrassmannIdentity` body (`grassmann_le_twice_moment`), and several imports of AnalyticMoment that sit outside the 170 reviewed files are not in this packet.
- **No Complexitylib sources are in this packet.** The Complexitylib obligation is only touched here at the boundary, through `ActualGraphEdges`, and stays open.
- **Nothing was run.** I used no tools and did not recompute any hashes. I cite declarations by name, not line number.
- **Axiom evidence is limited to roots.** Only the fresh-173 roots and the constants they reach carry axiom evidence. Modules marked `transitively_consumed:false` are compiled but have no axiom profile.

## File coverage (42 of 42 inspected)

| Group | Files | Consumed (per pins) |
|---|---|---|
| Material support | ActualFiniteMomentLpBounds, ActualFixedFunctionalAppendOperator, ActualFixedFunctionalBinaryMatrixMoment, ActualComplementCoordinateMassBridge, ActualCmmsaParameterReconciliation, ActualCmmsaAdmissibilitySelector, ActualFiniteLaw | all true |
| Source reduction | ActualOccurrenceAllocation, ActualEqualityCloud, ActualGraphEdges, ActualFinite3LinSource | true |
| | ActualEqualityCloudDegree, ActualGraphIncidence | false |
| Checks harnesses | A12InfluenceBound, A20SquareGlobalness, A21DyadicMoment, and the A8 checks (AmbientAssembly, AveragedAssembly, AveragedTransport, Endpoint, EnergyNaturality, PairAssembly) | false |
| HC46 side modules | A9ActualFiber, CommonDerivative, FinitePeeling, MixedPeeling | false (zero reached constants, matching the prior R9 finding) |
| MZ24 / sampling | ActualMZ24FixedZoomListBound, ActualMZ24ComplementRestriction, ActualMZ24DistinctPairAggregation, ActualMZ24GenericSubfamilyRepresentative, ActualFiniteIncidenceSampling | false |
| Leaf, clique and functional | ActualLeafTransport, LeafRelationLaws, LeafTransportCoherence, LeafPresentationDescent, LeafCenterRestriction, LeafRepresentativeSampler, LeafRejectionUnion, CliqueCollisionTransfer, CliqueJointLaw, CliqueScoreTransfer, CompatibleRhsFunctional | false |

## Results for the material-relevant files

**Same material I/copies/U/A/C/T/f (CoordinateMassBridge).** The `matchingStarMass` and `matchingCenterMass` on a side complement A are shown equal to their counterparts on `CoordAmbient J = Fin (2J) → F₂`.
- The proof rests on `starLaw_pushforward_actual`, which shows that a uniform law pushed forward along an equivalence stays uniform.
- On the coordinate side, the tables `selectedCoordinate*Table` are the transported I/copies/U/A tables and `coordinateFunctional f` is the transported functional, all through the same `actualCoordinateEquiv`.
- The basis is fixed by `finBasisOfFinrankEq`. The identity holds for that basis, and every downstream definition uses the same one.

**Moment identity (BinaryMatrixMoment, AppendOperator).**
- `matrixMoment` equals `actualBinaryMatrixMoment`, which equals `actualAppendRankImageMoment`, and both steps are exact.
- The base matrix is uniform over all n×c matrices. One base is shared across all k independent appended draws, and each appended draw is unconditional.
- `rawG` and `rawF` agree with `rankImageBoolean` on rank-deficient arrays as well (both give 0).
- The order "base columns, then appended columns" is preserved by `finSumFinEquiv`.
- `appendBinaryMatrix_injective_iff` and `appendBinaryMatrix_range_eq_span` are correct.

**Direction.** The packet proves `matchingStarMass ≤ 2·moment`, which is the upper bound the material route needs. It depends on `hdV`, `hD` and `hsmall` (which is (c+ks)·2^{c+s−1}/2^n ≤ 1/2), and on `grassmann_le_twice_moment`, whose body is in another packet.

**LpBounds.** All of these are unconditional for p ≥ 1, and the direction is correct in each:
- Jensen on an append fibre.
- `appendAverage_lpMoment_le`: the two-stage uniform equals the full uniform via the append equivalence, and no rank-conditioned law appears.
- Normalized Minkowski, including the empty family.
- The power-mean bound with cost card^{p−1}, which matches the earlier finding of an (r+1)^m low-part factor.

**Cmmsa arithmetic.**
- `hn_handoff`: (8·gap/16)^{m+1}·gap^{−(m+1)} = 2^{−(m+1)} ≤ 5/8. It needs the explicit premise `16 ∣ gapRoot`.
- `amplified_leaf_fit_of_hBlock`: d·R + 1 ≤ L follows from R ≤ ⌊(L−1)/d⌋.
- `admissible_eventually` holds for every threshold function `sourceHMin`. `selector_spec` and `selector_unbounded` are correct, and the selector returns `⊥` when the admissible set is empty, so there is no default-value masking.

**Peeling closed forms (not consumed).**
- Σ_{i<k}(2 + 4(r+i+1)) = 4rk + 2k² + 4k. ✓
- The mixed version gives 4r(k+l) + 2(k+l)² + 4(k+l). ✓

**Johnson / list bound (not consumed).** Using centred one-hot vectors: N·O·c ≤ ⟨S,R⟩ ≤ √(N·O)·√O, so N·c² ≤ 1. With 4/2^{d−a} < β this gives |list| ≤ 16/β². ✓

**Incidence sampling (not consumed).**
- Var ≤ μ, so μ·TV² ≤ 1/4 (the proof states the slacker bound ≤ 1).
- Chebyshev gives P ≤ 1/(ε²μ). ✓

**Source reduction.**
- The equality cloud has an exact minimum equal to the sum of mismatches.
- Distinct rows intersect in at most one variable, even when owners repeat.
- Each port touches at most 3 incident edges, and each internal variable has degree exactly 2.
- The row count is 4|E|, so the size blow-up is linear given a constant degree.

## Findings

| ID | Severity | Declarations | Finding and disposition |
|---|---|---|---|
| C1 | Medium (numeric/runtime gate) | `Admissible`, `admissible_eventually`, `selector` | Nonemptiness needs bOf(m) = 4000m² ≤ √log₂L with m ≥ 256, which means log₂L ≥ about 6.9×10¹⁶. "Eventually" comes with no rate, and the selector is `noncomputable`. This is asymptotic existence only. Runtime and polynomial-size questions are **open**. |
| C2 | Medium (Complexitylib boundary) | `crossing_card_eq_cut`, `crossing_expansion`, `outgoing_eq_actual_darts` | These rely on `FixedPortCycleFamily.kappa`, `cut_expansion`, `Complexity.RegGraph.dartsBetween` and `ExpanderCutInstantiation.support`, none of which are in this packet. Still to check elsewhere: κ > 0, whether the family is constructed or assumed, ExpanderPad padding and reindexing, computability of the ZigZagBaseExists/ExpanderRandom base, and coverage for every n including small n. **Open.** |
| C3 | Medium (cross-packet) | `matchingStarMass_cast_le_twice_*` | Depends on `hsmall`, `hD` and `MatrixGrassmannIdentity.grassmann_le_twice_moment`. Discharging these at the selected c, s, k, J is an **integration** item. |
| C4 | Medium (fidelity, not consumed) | `tD`, `inputExponent`, `E1_not_75/150/225` | The exponents involve factorials of 2^{2+1000D⁵}. The formal output exponent (47/127/216) is explicitly proved to differ from the 75/150/225 values, which presumably come from the manuscript. Flag for the manuscript audit; no credit given. |
| C5 | Low (warning disposition) | ActualLeafRejectionUnion | `set_option linter.unusedVariables false` suppresses warnings rather than fixing them. Zero owned warnings is not the same as clean. |
| C6 | Low (provenance) | ActualEqualityCloudDegree header ("Uncompiled source draft"); LeafRepresentativeSampler | The header is stale: the file sits in the compiled closure. The second file defines no sampler. No weight given either way. |
| C7 | Info | `finite_qary_list_bound` (`hinj` unused), `hn_handoff` (`_hm` unused), commented-out `finite_johnson_count`/`symbolCount` blocks in FixedZoomListBound | Hygiene only. The commented-out proofs are unverified and must not be cited. |
| C8 | Info | CoordinateMassBridge (`respectTransparency false`, 400k heartbeats), local `Fintype.ofFinite` instances | These affect elaboration only. Keep them for replay. |
| C9 | Info | Checks harnesses | The A8, A12, A20 and A21 `#print axioms` names match the fresh-173 stdout. `#check`-only items such as `a20Mean`, `a8T2AllPairEquiv` and `a8NestedDomainEquiv` are not roots. I give them no axiom credit, only reached-constant status if they turn out to be reached. |
| C10 | Info | All `consumed:false` modules above | Compile evidence only, with no axiom profile and no credit. |

## Safe conditional claim for this packet

The following holds under pinned Init/Mathlib/Batteries trust, the native receipts, and the cross-packet inputs named above (`grassmann_le_twice_moment`, `FixedPortCycleFamily`, `ActualPresentedLeafGluing`, `ActualStarSpanIntersection`, `ActualOccurrenceCounts`):

1. **Coordinate transport.** For each selected side complement, the star and center matching masses transport exactly to `Fin (2J) → F₂`, with the same transported tables and functional.
2. **Moment identity.** The fixed-functional `matrixMoment` exactly equals the unconditional appended-matrix rank-image moment with a shared base.
3. **Star-mass bound.** Star mass is at most twice that moment, given `hdV`, `hD` and `hsmall`.
4. **Finite inequalities.** Finite Jensen, Minkowski and power-mean inequalities hold for natural p ≥ 1 on the uniform matrix measure.
5. **Cmmsa arithmetic.** The arithmetic handoff and the "eventually nonempty" selector are proved for any threshold function.
6. **Source combinatorics.** The equality-cloud and occurrence-allocation combinatorics are exact.

Not covered by this claim: the removal of hHC from the material export, Spectral47, `hfail` usefulness, numeric NO, κ and the expander construction, encoded reduction, runtime and learning, manuscript fidelity, total warnings, and any acceptance.

## Questions carried to integration

1. Discharge of `hsmall`, `hD` and `hdV` at the instantiated (c, s, k, J), and the review of the `MatrixGrassmannIdentity` body.
2. Complexitylib (C2): the 23-module review, κ > 0, whether `FixedPortCycleFamily` is constructed or rests on a hypothesis, the padding constants, and computability.
3. Where the material root chains in the C1 selector, and whether any runtime claim depends on L.
4. Remaining out-of-170 material bodies not in this packet: SelectedSpectralParameters, AppendFourierCrossLevelOrthogonality, RankImageRightBasisInvariance, the Tagged and OrdinaryStar families, SamplerParameters, and StarFixedRhoDimensionGuard.
5. Manuscript check of the E1 exponents (C4) and the Cmmsa constants (4000m², /16, 5/8).
