# Non-claims review, Full90 material packet 2 of 5

## Verdict: GO-WITH-NOTES, for this packet only

This verdict covers only the 42 files supplied in packet 2. It is not a verdict on material readiness, on the export, or on the manuscript, and it does not endorse Root's preparation.

- **Coverage.** All 42 supplied files were inspected and none were skipped. No body that this packet was required to carry is missing.
- **Defects.** None found. I found no vacuous statement, no reversed inequality, no hidden hHC premise, and no `sorry`, `axiom`, `native_decide`, `implemented_by` or `unsafe` anywhere in the text.
- **How I reviewed.** I read the text only. I used no tools, ran no Lean or Lake, wrote nothing, started no subagents, and recomputed no hashes. Without tools I could not count lines, so findings cite declaration names. I checked each statement's hypotheses, quantifiers and direction, and recomputed the arithmetic by hand. That the files compile rests on the native receipts.
- **Limits.**
  - **No Complexitylib files are in this packet.** The Complexitylib boundary is not reviewed here, and one file in this packet depends on it (finding N7).
  - **The export is not in this packet.** `ActualSelectedComplementHC46OriginalApplication.lean` holds the exported conclusion and its guards, so I could not verify them here. What this packet does contain is the coordinate and moment identities the export depends on (N3).

## Coverage and evidence tier for each file

"Consumed" is the `transitively_consumed` pin. Even in a consumed module, only the constants the trace actually reaches carry fresh axiom profiles. Per-constant membership was not supplied. Modules marked "compile only" have no axiom profile at all.

| # | File | Status | Consumed |
|---|---|---|---|
| 1–9 | Harness files: A12InfluenceBoundChecks, A20SquareGlobalnessChecks, A21DyadicMomentChecks, A8AmbientAssemblyChecks, A8AveragedAssemblyChecks, A8AveragedTransportChecks, A8EndpointChecks, A8EnergyNaturalityChecks, A8PairAssemblyChecks | Inspected; they contain only `#check` and `#print axioms` | No |
| 10 | A9ActualFiber | Inspected | No |
| 11 | CommonDerivative | Inspected | No |
| 12 | FinitePeeling | Inspected | No |
| 13 | MixedPeeling | Inspected | No |
| 14–16 | CliqueCollisionTransfer, CliqueJointLaw, CliqueScoreTransfer | Inspected | No |
| 17 | CmmsaAdmissibilitySelector | Inspected | **Yes** |
| 18 | CmmsaParameterReconciliation | Inspected | **Yes** |
| 19 | CompatibleRhsFunctional | Inspected | No |
| 20 | ComplementCoordinateMassBridge | Inspected | **Yes** |
| 21 | EqualityCloud | Inspected | **Yes** |
| 22 | EqualityCloudDegree | Inspected | No |
| 23 | Finite3LinSource | Inspected | **Yes** |
| 24 | FiniteIncidenceSampling | Inspected | No |
| 25 | FiniteLaw | Inspected | **Yes** |
| 26 | FiniteMomentLpBounds | Inspected | **Yes** |
| 27 | FixedFunctionalAppendOperator | Inspected | **Yes** |
| 28 | FixedFunctionalBinaryMatrixMoment | Inspected | **Yes** |
| 29 | GraphEdges | Inspected | **Yes** |
| 30 | GraphIncidence | Inspected | No |
| 31–37 | LeafCenterRestriction, LeafPresentationDescent, LeafRejectionUnion, LeafRelationLaws, LeafRepresentativeSampler, LeafTransport, LeafTransportCoherence | Inspected | No |
| 38–41 | MZ24ComplementRestriction, MZ24DistinctPairAggregation, MZ24FixedZoomListBound, MZ24GenericSubfamilyRepresentative | Inspected | No |
| 42 | OccurrenceAllocation | Inspected | **Yes** |

**Totals.** 11 files are consumed. The other 31 (the 9 harnesses plus 22 bodies) are compile-only and must not be credited with axiom profiles.

**Harness cross-check.** Every `#print axioms` target in the 9 harness files appears by name in the fresh 173-root stdout. Each listed profile is a subset of {propext, Classical.choice, Quot.sound}; for example `a21_exponent_le` lists only propext. The A12 harness has 19 targets and the stdout has 19 matching entries. The harness outputs themselves were not supplied, and these files are not evidence.

## What I checked in the consumed files

### FiniteMomentLpBounds
- `appendAverage_abs_pow_le` is Jensen's inequality on one genuine append fibre.
- `appendAverage_lpMoment_le` holds because the two-stage uniform draw equals the uniform full-matrix draw, by a bijection.
- `lpNorm_add_le` is Minkowski's inequality. The normalisation factor N^(1/p) is moved through correctly, and the theorem needs p ≥ 1.
- `finite_sum_lpNorm_le` handles the empty family correctly: its lpNorm is 0^(1/p) = 0 because p ≥ 1.
- `finiteLevel_sum_abs_pow_le` and `finiteLevel_lpMoment_aggregate_le` carry a card^(p−1) factor, and the empty and p = 1 edge cases are correct.
- **All of these hold on the unconditional uniform carrier only.** None of them may be applied under a rank-conditioned law without a separate argument.

### FixedFunctionalBinaryMatrixMoment and FixedFunctionalAppendOperator
- The coordinate-to-matrix map is a transpose bijection. Base columns come first, then appended columns, using `finSumFinEquiv`.
- `rawG` and `rawF` match `indicator ∘ rankImageBoolean` for every input, including rank-deficient ones, which score 0 on both sides.
- In `actualAppendRankImageMoment`, one shared base matrix M is raised to the power `appendAverage(...)^k`. That is exactly k independent append draws from a common base.
- The conclusion of `matchingStarMass_cast_le_twice_actualAppendRankImageMoment` is an upper bound, matching star mass ≤ 2 × the moment. Scoring rank-deficient matrices as 0 only makes the right-hand side smaller, so the direction is sound.
- **It is conditional** on `hdV`, `hD : 0 < c+s` and the numeric premise `hsmall`.

### ComplementCoordinateMassBridge
Every Grass and Extension map below is a genuine bijection, and the equalities are exact, not inequalities.
- The selected side complement `A` (dimension 2J) maps to `Fin (2J) → ZMod 2` through a basis chosen by `Module.finBasisOfFinrankEq`.
- `starLaw_pushforward_actual` holds by `pushforward_uniformLaw_equiv`.
- `matchesStar_coordinate_iff` gives exact event equivalence.
- `matchingStarMass_actual_coordinate` and `matchingCenterMass_actual_coordinate` are equalities. The same `I`, `copies`, `U`, `A`, `C`, `T` and `f` appear on both sides, through `transportedCenter/LeafTable`, `selectedCoordinate*Table` and `coordinateFunctional`.

### CmmsaParameterReconciliation
- `hn_handoff`: 8·sigmaBase = g/2, so (g/2)^(m+1)·g^−(m+1) = 2^−(m+1) ≤ 5/8. Checked.
- `old_sigma_route_failure` correctly shows that the R/8 route exceeds 1.
- `amplified_leaf_fit_of_hBlock` and `RBlock_le_blockNum` are correct.
- Because `m ∣ hBlock`, `gapRoot` is exactly R^(1−1/m).

### CmmsaAdmissibilitySelector
- `admissible_eventually` gives K ≥ m², b² and d+T, which yields log blockNum ≥ T and then hBlock ≥ max(sourceHMin m, 4m) and sigmaBase ≥ 8. Checked.
- `selector_spec`, `selector_eq_bot_iff` and `selector_unbounded` are correct. The empty case is represented by `⊥`, so no default value hides it.

### FiniteLaw, OccurrenceAllocation, EqualityCloud, GraphEdges and Finite3LinSource
These are the finite-law calculus and the definitions of instance and row types. They are internally consistent, with intersections ≤ 1, `exact_minimum` attained, and the representative bijection proved.

## Findings

| ID | Severity | Declarations | Finding and disposition |
|---|---|---|---|
| N1 | Medium (evidence scope) | All 31 compile-only files; unreached constants in the 11 consumed files | Compiling does not give a declaration a standard axiom profile. Only constants that the 173 roots actually reach carry fresh profiles, and per-constant reach was not supplied. *Retained.* |
| N2 | Medium (scope of material claims) | `matchingStarMass_cast_le_twice_actual{BinaryMatrix,AppendRankImage}Moment` | This is one fixed (C, T, f), conditional on `hsmall`. It does not bound star acceptance taken over a selection or union of functionals; that is the source/star lane, which stays open. *Do not cite it as a star or acceptance result.* |
| N3 | Medium (cross-packet) | Coordinate bridge plus the export | The export and AnalyticMoment are in another packet. Integration must confirm two things. First, the export applies this bridge and the append bound to the **same** `A` and to `selectedCoordinate*Table` / `coordinateFunctional`. Second, it **derives** `hsmall` and `hdV` rather than assuming them. Not checkable here. |
| N4 | Medium (parameters / numeric NO) | `hn_handoff`, `Admissible`, `selector_*`, `sigmaRepair`, `sigmaFinal`, `Gamma`, `gammaFinal` | **(a)** The HN premise `hzeta` is assumed, not proved. **(b)** `sourceHMin` is a free threshold, and the source theorem is not supplied. **(c)** The /4, /2 repair steps and the Gamma bound are definitions only; no theorem proves them. **(d)** `L0` is existential and astronomically large. **(e)** `16 ∣ gapRoot` follows from `8 ≤ sigmaBase` but is not exported as a theorem. *Gives no numeric-usefulness result.* |
| N5 | Medium (manuscript fidelity) | `E1_not_75`, `E1_not_150`, `E1_not_225`; `geometricOutputExponent` | These theorems record that the formal exponent (47, 127, 216) differs from 75, 150 and 225, which appear to be manuscript values. They look like a documented formal-versus-manuscript mismatch. The module is compile-only and not consumed. *Retain for the fidelity gate.* |
| N6 | Medium (reduction) | `OccurrenceAllocation.*`, `EqualityCloud.*`, `Finite3LinSource.ofActual*` | The material route reaches these modules only for instance and row **types**. No theorem here connects violations of the source instance to the allocated instance; there is only the per-cloud `exact_minimum` given fixed ports. *Encoded-reduction correctness remains open.* |
| N7 | Medium (Complexitylib boundary) | `GraphEdges.crossing_expansion`, `crossing_card_eq_cut` | These depend on `Complexity.RegGraph.dartsBetween`, `FixedPortCycleFamily.cut_expansion` and `kappa`, and on `ExpanderCutInstantiation`, which is pinned as not consumed. So the expansion constant rests on the unreviewed Complexitylib expander interface. It is unknown whether `crossing_expansion` is reached. *Must not be treated as reviewed or proved by citation.* |
| N8 | Low (warning disposition) | `LeafRejectionUnion` sets `linter.unusedVariables false`; binders that look unused: `hp` in `appendAverage_abs_pow_le`, `hinj` in `finite_qary_list_bound`, `hQW` in `complementComponentEquiv`, `had` in `complementTable`, `_hm` | Warnings are being suppressed, and several binders look unused. Integration should reconcile this with the claim of zero owned warnings and check the linter configuration. Zero owned warnings is not zero total warnings, and suppressing a warning does not dispose of it. *Open.* |
| N9 | Low (stale or overstated text) | `EqualityCloudDegree` header ("Uncompiled source draft"); `A9ActualFiber` header; `MZ24FixedZoomListBound` (large commented-out blocks of an earlier proof) | These carry no evidential weight. `A9NormalizedInitialMap` uses the InitialGraph convention B0 ⊆ B (prior packet 5, finding F4), not the ambient fibre, so it must not be cited as A11's fibre count. |
| N10 | Info | Clique\*, Leaf\*, MZ24\*, FiniteIncidenceSampling, CommonDerivative, Finite/MixedPeeling | This is conditional infrastructure, compile-only. `collisionMass`, `PairSubindependent`, `hcodim` and `hforce` remain explicit premises, and nothing extracts the subfamily or the decoder. The `MixedPeeling` closed-form loss exponent 4r(k+l) + 2(k+l)² + 4(k+l) re-derives correctly. |
| N11 | Info | Elaborator settings: `respectTransparency false`, `maxHeartbeats 400000`, `maxRecDepth`, `exponentiation.threshold` | These affect elaboration only; the kernel still re-checks the proofs. Record them for replay. |
| N12 | Info | `actualCoordinateEquiv` | The coordinate tables depend on a basis chosen classically. Only the masses are basis-invariant. Any later numeric claim must hold for every basis; the universal contracts do. |

## Safe conditional claim (this packet)

Assuming the pinned kernel and library trust, the native compile receipts, and the external definitions this packet relies on, the following hold:

- For each selected side complement `A` and fixed tables C, T and functional f, the star mass and center mass equal their coordinate transports **exactly**.
- For a fixed (C, T, f), and under `hdV`, `0 < c+s` and `hsmall`, matching star mass ≤ 2 × the actual unconditional append rank-image moment, with rank-deficient matrices scoring 0.
- The finite Jensen, contraction, Minkowski and level-aggregation inequalities hold on the uniform matrix carrier.
- The CMMSA selector is eventually nonempty and unbounded for **every** supplied threshold function.

**Not claimed:**
- the exported material conclusion;
- `hsmall` being discharged;
- star or source acceptance;
- Spectral47;
- numeric NO;
- reduction correctness;
- the expander constant or anything about Complexitylib;
- manuscript fidelity of E1, Gamma or sigma;
- axiom profiles for any of the 31 compile-only files;
- zero total warnings.

## Questions to carry to integration

1. What is the exact statement of `selected_actual_material_moment_bound_original`, and how does it use N3? It must remove only `hHC` and keep `hSpectral`, the selector, failed-zoom, strict rank and positive-parameter premises.
2. The definitions this packet's statements depend on: `matchingStarMass`, `matchingCenterMass`, `MatchesStar`, `center/leafMatchBit`, `rawG`/`rawF`/`rawTF`/`matrixMoment`, `grassmann_le_twice_moment`, `rankImageBoolean`, `transportedCenter/LeafTable`, `TaggedGoodU`, `SideComplement`/`sideComplement_finrank`, `lpNorm`/`lpMoment`, `EqualityGadget`, `ActualPresentedLeafGluing`, and `ActualOccurrenceCounts.rows_eq_map`.
3. Per-constant trace reach for GraphEdges, Finite3LinSource and the Cmmsa modules.
4. Where `sourceHMin` is instantiated, and how it relates to the Spectral47 cutoff (`analyticSourceHeightFloor`).
5. The Complexitylib review of `FixedPortCycleFamily.cut_expansion` and `kappa` against the 23 Complexitylib bodies supplied in other packets.
6. The linter configuration behind N8, and the disposition of the inherited warning debt.

Still open: Spectral47; useful numeric NO; source, star and robust8S; encoded reduction, runtime and learning; the original upstream builds and bridges; warning disposition; a fresh-checkout replay; manuscript fidelity, render, novelty and citations; and the final full-scope providers.
