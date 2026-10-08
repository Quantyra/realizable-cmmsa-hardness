# Proof-adversarial review: Full89 partition 8 of 9

**Verdict: GO-WITH-NOTES.** This covers partition 8 only, not the whole campaign.

I read all 45 supplied files in full. I found no proof-level defect: no theorem is vacuous, no quantifier is weakened, no exponent bound is wrong and no proof argues in the wrong direction. The notes below are about where files came from, statement hygiene, and questions that integration has to answer. I could not compile anything, and I did not check the SHA256 values. Whether these files compile rests entirely on the GCP evidence in the packet.

## Scope

- **What this partition contains:** support lemmas for A1, A14 and A15 (line and hyperplane versions, raw/actual/typed/complex/intrinsic variants), Grassmann counting, flag posterior, and the matrix-lift comparison (homogeneous, affine target, exact budget, full row rank).
- **A22 and HC46 are not stated here.** No declaration has a real `q` or an `η` parameter, and none takes an `hHC`-style hypercontractivity premise. Auditing unrestricted-η HC46 and real-q A22 with the same selected consumer has to happen in the partitions that state them.
- **The only HC-shaped statements are trivial.** `BinaryMatrixFourier.binary_hc_rankZero` and `binary_hc_rankZero_exact` are the rank-zero slice: the factor `2^(500·0²·p)` is 1, and the bound is just `δ ≤ δ^(1−2/p)` for δ in [0,1]. The file header says outright that the analytic HC inequality is not asserted. Nothing downstream should cite these as HC evidence.

## File inventory (45 supplied, 45 inspected, 0 skipped)

All were inspected in full:

1. BinaryMatrixA1Complex
2. BinaryMatrixA1Composition
3. BinaryMatrixA1NestedCarrier
4. BinaryMatrixA1Phase
5. BinaryMatrixA1TypedFourier
6. BinaryMatrixActualAffine
7. BinaryMatrixActualAffineCarrier
8. BinaryMatrixCodomainA14
9. BinaryMatrixCodomainA15
10. BinaryMatrixComplexA14
11. BinaryMatrixComplexA15
12. BinaryMatrixFirstDerivative
13. BinaryMatrixFourier
14. BinaryMatrixHybridSelector
15. BinaryMatrixLineA14
16. BinaryMatrixLineA15
17. BinaryMatrixLineTranslation
18. BinaryMatrixNestedSelectorA1
19. BinaryMatrixTypedA14FixedBase
20. BinaryMatrixTypedA14Hyperplane
21. BinaryMatrixTypedA14HyperplaneFixedBase
22. BinaryMatrixTypedA14HyperplaneReduced
23. BinaryMatrixTypedA14Line
24. BinaryMatrixTypedA14Reduced
25. BinaryMatrixTypedA15AdaptedGlobal
26. BinaryMatrixTypedA15Hyperplane
27. BinaryMatrixTypedA15HyperplaneGlobal
28. BinaryMatrixTypedA15HyperplaneReduced
29. BinaryMatrixTypedA15HyperplaneReducedGlobal
30. BinaryMatrixTypedA15OneStep
31. BinaryMatrixTypedA15Reduced
32. BinaryMatrixTypedA15ReducedGlobal
33. BinaryMatrixTypedA15Transport
34. BinaryMatrixTypedHyperplaneIntrinsicP
35. BinaryMatrixTypedHyperplaneSelector
36. GrassmannCounting
37. GrassmannFlagPosterior
38. MatrixFullRowRankHalf
39. MatrixGrassmannFibre
40. MatrixGrassmannIncidence
41. MatrixGrassmannIntersectingAnchor
42. MatrixGrassmannMoment
43. MatrixLiftAffineTarget
44. MatrixLiftExactBudgetZoom
45. MatrixLiftFullRowRankBridge

## What I checked and found sound

**A15 (one-step bound):**
- In `upToRawSquareGlobal_lineP` and `complexLineP_raw`, the pointwise step uses `(z−aw)² ≤ 2z² + 2a²w²`.
- The averaging step is Jensen's inequality (`sum_div_card_sq_le_sum_sq_div_card`), and translation preserves the budget.
- The constants combine as `2(1+b²)·2(1+a²) ≤ 4a²·4b²/… = 4b⁴`, with a = 2^j and b = 2^(j+1) = 2a, so b⁴ = 4a²b². The resulting factor is `4·2^(4(j+1))`, which is correct.
- The direction is right: order k+1 in the premise gives order k in the conclusion, and `liftRestriction_budget` adds exactly one equation.
- Empty fibres evaluate to 0/0 = 0. Every bridge that needs this carries an explicit `0 ≤ ε`, and actual fibres are never empty because the base lies in the fibre.

**A14:**
- `rankProjection_rawRestrict_lineP_eq_hybridDerivative` aggregates colliding induced frequencies through the full reduced rank projection.
- Its case split is exhaustive: a selected Y has rank = drop-rank + 1 (`rank_eq_drop_add_hybrid_indicator`), and a drop-rank ≠ j kills the term on both sides.
- The scalar identity `lineP_scalar_at_adjacent_rank` checks out from the multiplier formula `lineTranslationMultiplier_eq_hybrid`.
- The typed fixed-base versions (`typed_A14_fixedLine`, `typed_A14_fixedHyperplane`) hold at an arbitrary base T.

**Intrinsic vs. coordinate presentations:**
- Over F₂, a line L has exactly one nonzero vector, so `lineScalarEquiv` is canonical, and `typedLineAverage` is defined intrinsically.
- A hyperplane H has exactly one defining functional ψ, so the complement choice is harmless. `intrinsicHyperplaneP_eq_typed` and `typedHyperplaneSelected_iff_ker_le` close the coordinate/intrinsic gap.

**A1:**
- `selected_nested_iff` and `derivative_composition_A1` are correct for arbitrary affine bases T and S.
- `manuscript_A1_complex` follows soundly by splitting into real and imaginary parts.
- Trace-character orthogonality and inversion (`carrierFourier_inversion`) are sound; the `≠ 0` witnesses come from projectivity.

**Matrix lift:**
- The factor-two step `affine_target_*` requires g ≥ 0, a surjective X₁, and a full-rank target B.
- `full_row_rank_gt_half` discharges the strict half count for c < k: it needs `2(2^c−1) < 2^k`, which follows from `2^(c+1) ≤ 2^k`.
- In `smaller_budget_zoom_density_le`, flag averaging handles empty refined zooms through a Gaussian count of zero, and its positivity divisor `gaussian(d−q)(a−q) > 0` holds.

## Findings

| # | Severity | Location | Finding |
|---|---|---|---|
| F1 | Medium (provenance) | Headers of GrassmannCounting, GrassmannFlagPosterior, MatrixGrassmannIncidence, MatrixGrassmannMoment, MatrixGrassmannFibre | Each header says "UNCOMPILED", "SOURCE DRAFT" or "no compiler result". That contradicts the packet's claim of seven zero exits and a 319-file source closure. Integration must confirm these five files are inside the compiled closure and fix the stale headers. If any of them is not compiled, its declarations are **INCOMPLETE**. |
| F2 | Low | BinaryMatrixTypedA15Hyperplane, last line | The file closes with `end BinaryMatrixTypedA15Hyperplane` after opening `namespace PvNP.RealizableHardness.BinaryMatrixTypedA15Hyperplane`. This closes only one component and leaves `PvNP.RealizableHardness` open at end of file. Lean accepts it, but it is hygiene. |
| F3 | Low | GrassmannCounting (`Frame`, `frameFinite`, `gaussian_of_lt`, …) and GrassmannFlagPosterior | Both files rely on autoImplicit for `a`, `d`, `n` and `J`, with no `set_option autoImplicit false`. The bindings are universal (no weakening), but they compile only under the project's default setting. Confirm that setting. |
| F4 | Low | MatrixLiftFullRowRankBridge: `binary_affine_target_score_sum_le_twice`, `…_mean_le_twice`, `…_zoom_density_le_two_e` | These are `def`s whose type is a Prop, with no written type, and `linter.defProp` is turned off. The trusted statement is therefore only the elaborated type and cannot be read from the source; it should be read from the trace. `columnLinear` is also defined twice, identically (MatrixFullRowRankHalf and MatrixLiftAffineTarget), and the two are bridged by unfolding. |
| F5 | Low (integration) | BinaryMatrixFourier: `PseudorandomExact`, `exactWholeRestriction` | "Exact raw budget" means nominal budget, and zero rows can pad it. So raw exact-r really quantifies over every actual order ≤ r, which makes it a stronger premise than the manuscript's actual exact-r condition. If the selected consumer uses it as the manuscript premise, the downward-closure argument has to be supplied elsewhere. For Grassmann zooms that argument exists in `smaller_budget_of_exact_r`; for matrix affine restrictions it does not exist in this partition. |
| F6 | Low | MatrixLiftExactBudgetZoom: `smaller_budget_of_exact_r`, `homogeneous_lift_density_of_exact_r` | The hypothesis `hrd : r < d` is stricter than the proof needs (`a ≤ d` only needs `r ≤ d`). Check that the consumer's instance never needs r = d. |
| F7 | Info | MatrixGrassmannFibre, MatrixGrassmannIncidence | They set `backward.isDefEq.respectTransparency false`. This affects only the elaborator, not the kernel. There are also `maxHeartbeats` increases in four typed files. |
| F8 | Info | BinaryMatrixA1Complex imports `Mathlib.Basic.Complex.BigOperators` | This module path is unusual. Confirm it resolves in the pinned Mathlib version. |
| F9 | Info | BinaryMatrixTypedA15HyperplaneReducedGlobal | Names such as `reducedCoordinateRestriction`, `reducedMatrix_mulVec` and `reduced_global_iff_coordinate` duplicate names in the opened `BinaryMatrixTypedA15ReducedGlobal`. Types disambiguate them, so this is a fragility risk for downstream `open`s, not an error. |
| F10 | Info | `typedLineSelected`, `hybridLineSelected` | Neither is formally tied to `BinaryMatrixNestedSelectorA1.Selected L ⊤`. They agree by definitional reading only, so the A1 selector and the A14 selectors are not connected by any theorem here. |

## Conditional vs. universal statements

- **Universal:** the A1 identities, the A14 identities (any base, function, rank or dimension), and the A15 bounds given `0 ≤ ε` and the up-to-(k+1) premise.
- **Conditional on explicit premises:**
  - affine-target comparison: on `hhalf` (discharged for binary C with c < k) and on `hzoom`, which is a local density premise.
  - exact-budget zoom: on `hexact`.
  - `eventPosterior_eq_conditional`: on `hpos`, with null mass defined as 0, not a normalized law.

## Questions left for integration

1. Definitions this partition imports but does not include:
   - `BinaryMatrixA1CoefficientTransfer` (`initialDerivative`, `nextDerivative`, `initialDerivative_fourierCoeff`)
   - `BinaryMatrixA1CharacterBridge` (`tracePair_matrix`, `traceCharacter_eq_matrix_character`)
   - `GrassmannIncidence` (`kernel`, `prior`, `conditional`, `adviceMarginal`, `incidenceCount_pos`), `TripleRestrictionRank` (`Draw`, `retained`), `VectorAdvice`, `PosteriorReweighting`

   `containmentProbability_formula` depends on `incidenceCount_pos`, whose premise needs `a ≤ J` and a matching dimension for `retained`.
2. A22 and HC46 with the selected consumer (unrestricted η, real q, no added `hHC`) are not in this partition.
3. F1 (the compile status of the five "UNCOMPILED" files) and F5 (whether `PseudorandomExact` matches the manuscript premise) need answers.
4. Library trust: Mathlib, Init and Batteries are taken from the pinned sources. I made no new-review claim about them.
5. Every gate the packet lists as open (Spectral47, the reduction/runtime/learning items, upstream bridges, manuscript, render and novelty) remains open. Nothing in this partition closes any of them.
