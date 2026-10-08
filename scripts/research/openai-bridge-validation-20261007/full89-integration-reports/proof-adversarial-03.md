# Full89 integration review, window 3/3 (carrier counting and transport): proof-adversarial lens

## Verdict

**For this window: GO-WITH-NOTES.** This covers only the carrier-counting and transport contracts whose full bodies were supplied here.

**For the whole integration: INCOMPLETE.** Every HIGH question from the earlier packets is still open. None of them can be settled from this window's source: the bodies of `OriginalExactInhabitant`, `OriginalApplication`, `AnalyticMoment`, `BinaryMatrixFourier`, `ActualBinaryMatrixHC46`, `A11`, `A22`, `RealQ*`, `DR6*` and `MatrixLift*` are not in it. GO-WITH-NOTES does not close any of those HIGH findings.

What I relied on, and what I did not check:
- No tools, writes, code, Lean/Lake or subagents were used.
- The SHA256 labels on the 12 window files match the all-170 pin list. I did not recompute the hashes from the content.
- The native exits, the 172 standard axiom profiles, the 319 source pins, the 566 unchanged objects and the trace identities are taken from the qualified receipts. I did not re-establish them.
- The pinned Init/Mathlib/Batteries code is trusted as library code. I did not review it.

## Bodies inspected (12 of 12; none skipped)

1. `ActualBinaryMatrixHC46A7T1Transfer` (300CD79D…)
2. `ActualBinaryMatrixHC46A7WeightedPredecessor` (775FFB87…)
3. `ActualBinaryMatrixHC46A8AmbientAssembly` (BE845673…)
4. `ActualBinaryMatrixHC46A8AveragedAssembly` (0C5D9127…)
5. `ActualBinaryMatrixHC46A8AveragedTransport` (83191C84…)
6. `ActualBinaryMatrixHC46A8Endpoint` (61387FFD…)
7. `ActualBinaryMatrixHC46A9AmbientFiber` (024850F6…)
8. `ActualBinaryMatrixHC46A9AmbientReindex` (5B4958CE…)
9. `ActualBinaryMatrixHC46CommonA16` (5B200903…)
10. `ActualBinaryMatrixHC46FourierA16` (21E062E1…)
11. `ActualTypedABFullA16Assembly` (BECC6381…)
12. `ActualTypedABFullA16Final` (A592FF69…)

The other 158 selected bodies are not in this window. Only their source, dependency and native identities are reused. Their prior lens verdicts are not reused as proof.

## Cross-partition contracts checked against the source in this window

**C1. A8 endpoint matches the A9 source exactly.** In `a8_output_q_le_actual_predecessor_sum`:
- The index is (A′, B′) with C ≤ A′ and B′ ≤ H.
- The guard is `A′ ⊓ (range X).comap C.mkQ = C ∧ B′ ⊔ (ker X).map H.subtype = H`. This is literally `a9AmbientA8SideConditions` with A=A′, A0=C, B=B′, B0=H.
- The summand `typedUniformMean (typedW6OutputEnergy A B Y (filteredCarrierFunction A B T f))²` is the same expression as the private `a9AmbientA8Energy`.
- k = finrank range X in both, and `a9AmbientA8PartitionEquiv` forces rank Y = rank X = k.
- The partition equivalence is an exact bijection. Its forward map derives rank preservation through `a9Ambient_A8_sideConditions_iff_rank_preservation`. Its backward map derives the side conditions through `a9Ambient_fiber_A8_sideConditions`.

**C2. The support case split is exactly complementary.**
- `a9Ambient_fixed_fiber_coarse_charge` needs `a+b+k ≤ D`.
- `a8_actual_energy_zero_outside_supported_window` gives zero energy exactly when `D < finrank A + finrank(W/B) + rank Y`.
- Both branches check out:
  - c > D: every level i ≤ D lies below the carrier.
  - c ≤ D: the support drop applies, with `rank Z ≥ rank Y` coming from `typedW6Precedes`.
- `hi : i ≤ a` follows from A0 ≤ A, and `hj : j ≤ b` follows from B ≤ B0, so a consumer can discharge both.
- `_horder` is unused and has to be supplied by the consumer (see N2).

**C3. The A8 transport has the right order.**
- The square stays inside both the T average and the S0 average.
- `a8_complex_normalized_mean_cube` gives E ≤ mΣe, then E² ≤ m²(Σe)² ≤ m³Σe². The complement count is cubed exactly once.
- S0 is removed only by `Equiv.addRight` on the ambient Hom group, and the `card ΩS` factor cancels.
- For each complement, the domain map (quotient chain using `range X ⊔ C = A2` and `H ⊔ ker X = ⊤`) and the kernel map (using `range X ⊓ C = ⊥` and `H ⊓ ker X = B2`) are genuine equivalences. So each complement contribution is exactly the typed energy on that complement.
- Graph charge: (u+v) ≤ cost ≤ D gives 3k(u+v) ≤ 6Dk. The bound holds with deliberate slack.

**C4. The A9 counts are exact.**
- The section fibre has 2^{k(a−i)} elements; the kernel of the quotient map V/A0 → V/A has dimension a−i.
- The extension fibre has 2^{k(b−j)} elements, using dim(B0/B) = b−j.
- The nested B0 count is [b, b−j]₂ = [b, j]₂. Annihilators enter only through the numerical symmetry, not through any map.
- `a7_a9_multiplicity_le` is the pure Gaussian/numeric bound. It is not one of the degenerate parent-family helpers.

**C5. The W6/T1 orientation and offset questions are settled.**
- In `a8_actual_energy_zero_outside_supported_window`, `typedW6Precedes A B Y Z` unfolds to `rank Z = rank Y + rank(Z−Y)`. That is the same orientation as `t1RankPrecedes X R`, which supports the `rfl` in `hactive_iff`.
- In `actualW6Derivative X 0 g` (used in `t1TypedW6_eq_actual` and in the A8 endpoint), the 0 is the affine base. The real base T is already carried inside `filteredCarrierFunction` or `actualDerivativeCoordinate`.
- This resolves complexity packet 3 N1/N3 and non-claims packet 3 F6.

**C6. A16 holds without any cost condition.**
- `filteredCarrierFunction_energy_le_A16` assumes only `ComplexFourierSupportedThrough D f` and `UpToActualNormSqGlobal D eps f`.
- eps ≥ 0 is derived, not assumed.
- When the carrier cost k > D, every level is annihilated. Retained levels each cost at most 2^{10D²}, are orthogonal across distinct residual ranks, and there are at most D+1 ≤ 2^{D²} of them, giving 2^{11D²}.
- This resolves proof-adversarial packet 2 F2 and complexity packet 2 Q2 (A20's unused `_hcost`).
- A16Final imports `A18SourceGlobal` only for its definitions and the nonnegativity lemma. It takes no influence premise.

**C7. The T1 transfer checks out.**
- `t1Triple_card` = 2^{dim A·dim(W/B)}.
- The ordinary/active correspondence is a bijection proved in both directions, with ordinary selection derived from activity.
- The full identity collapses ambient frequencies with collisions retained.
- How the count is used by A6's Hölder exponent is not in this window.

## Findings and dispositions

| ID | Severity | Declarations / evidence | Disposition |
|---|---|---|---|
| N1 | **Medium** | Bodies in this window import modules that are **not** among the 170 selected bodies: `ActualBinaryMatrixHC46A9ActualFiber` (imported by A9AmbientFiber), `ActualBinaryMatrixHC46CommonDerivative` (CommonA16, A16Final), `ActualBinaryMatrixHC46MixedPeeling` and `…FinitePeeling` (FourierA16, CommonA16). FourierA16 uses `mixedCoordinatePeel_rankProjection_eq_derivativeChain`, defined in MixedPeeling. | **Retained, bounded.** It is acceptable only if the exact172 trace shows zero reachable constants in those modules for all four consumers. The constants this window's critical path actually uses (`rankProjection_inner_eq_zero`, `complexEnergy_finite_sum_of_orthogonal`) depend only on Parseval and uniformMean. Integration must confirm from the trace that no reachable constant lies outside the 170 bodies. |
| N2 | Low | `a8_output_q_le_actual_predecessor_sum`: `_horder : a6Order t ≤ D` is unused. | Retained as a consumer obligation for A11; cannot be checked from this window. |
| N3 | Low | Private `a9AmbientA8Energy`, `finalEnergy`, `complexRealDot` appear in public statements. | Sound. A11 has to match them by unfolding; it compiled per the receipts. |
| N4 | Info | `a8_supported_graph_charge` proves 2^{3Dk} but states 2^{6Dk}. | Valid. Whether this matches the manuscript's exponent is a manuscript gate and stays open. |
| N5 | Info | Global (non-local) instances `a9AmbientLinearMapFintype` and `a9AmbientQuotientFintype`; duplicated real-dot definitions; `try simp only` in `a8_common_S0_filter_shift`; `with_unfolding_all`; `respectTransparency false`. | These affect elaboration and robustness only. The kernel re-checks every proof. |
| N6 | Info | Docstrings in AveragedAssembly/Transport saying "accepted with notes against frozen run 46/56"; stale docstrings in WeightedPredecessor; the mid-file `end` in WeightedPredecessor. | These carry no evidentiary weight either way. |

### Earlier HIGH and Medium questions, as they stand after this window

- **Proof-adversarial packet 7 F1, complexity packet 7 F1, non-claims packet 7 F1 (hHC in the material consumer): RETAINED.**
  - Logical availability: if `original_HC46_exact` has exactly the type `HC46ExactContract`, it can be supplied as `hHC` to `selected_actual_material_moment_bound`. Root reports this at line 144, but the body is not in this window, so I did not confirm it.
  - Dedicated export: none of the 172 roots is a composed hHC-free material bound. Only `selected_leaf_HC46_original` and `…failed_zoom…` exist.
  - The material bound also still assumes `hSpectral` (Spectral47 is open).
  - So no material-moment, reduction, runtime or learning acceptance follows.
- **Proof-adversarial packet 7 F2 (vacuity of the contract under exact-budget padding and eta < 0): RETAINED.** The relevant bodies (`BinaryMatrixFourier` lines 324–403, `ActualBinaryMatrixHC46` lines 111–150) are not in this window. Root's disposition that padding makes the whole fibre available, and so forces eta ≥ 0 including the zero-density branch, is unconfirmed here.
- **A11's strict lower-degree hS discharge, its A9 partition at lines 550/553, and the coarse charge at line 713: RETAINED.** This window confirms only the contracts A11 consumes (C1, C2, C4). The summation swap, the case split, the (i,j,k) aggregation and the hS discharge happen in A11.
- **A9 legacy route: PARTIALLY RESOLVED.** No body in this window references `a9_initial_datum_card`, `a9_fiber_triple` or the degenerate A7 parent-family lemmas. Absence across the whole repository is not claimed.
- **Not addressable from this window:** PseudorandomExact being one-sided, nominal-budget padding and flag averaging, the strict rank guard, the same pre-drawn T/f, the factor 2, DR6 signed incidence and normalization, the A18/A21/A22 constants, real-q `pConjugate` scope, the A14/A15 typed definitions beyond their uses in A16, and the inferred-type bridge aliases. All of these are retained.

## Open questions for other windows

1. Does the trace show zero reachable constants in MixedPeeling, FinitePeeling, CommonDerivative and A9ActualFiber, or in any other module outside the 170 bodies (N1)?
2. What is the exact type of `original_HC46_exact`? Does any root instantiate `selected_actual_material_moment_bound` with it?
3. Do the bodies of `PseudorandomExact`, `exactWholeRestriction` and `boolean_mean_le_of_exact` support the non-vacuity and eta ≥ 0 disposition, including the zero-density branch?
4. Does A11 discharge `_horder`, perform the a+b+k ≤ D / > D split, and sum over (i, j, k) using `a9AmbientA8PartitionEquiv` without the legacy helpers?
5. Manuscript fidelity of 6Dk, 3D(i+j+k), 11D² and 10D².

## What can safely be claimed

Within this window, assuming the qualified native receipts and pinned library trust:
- The A8 output-Q endpoint charges arbitrary complex input to the actual ambient final predecessors with factor 2^{6Dk}, keeping the square inside both base averages.
- The A9 fixed-final fibre has the exact Gaussian-times-graph count.
- The A8 predecessor sum is in exact bijection with the union over rank-k final maps of their A9 fibres.
- The energy outside the supported window is exactly zero.
- A16 holds for every carrier with no cost premise.
- The T1 transfer is an exact, unconditional identity.

Nothing here establishes that the full A22/HC46 milestone is accepted. Nor does it establish the hHC-free material moment, Spectral47, numeric NO bounds, the reduction, runtime or learning results, the upstream or fresh-checkout gates, or any manuscript, render or novelty verdict. Inherited warning debt remains open.
