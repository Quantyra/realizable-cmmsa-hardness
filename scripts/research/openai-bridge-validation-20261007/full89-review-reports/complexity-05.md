# Complexity review, partition 5 of 9: Full89 original A22/HC46/selected-consumer milestone

**Verdict for this partition: GO-WITH-NOTES.** This covers only the 16 files in this packet, not the whole campaign. I found no blocker or high-severity issue. All findings are low or informational, and several questions are left open for integration.

**Method.** As instructed, I used no tools. I did not open the source index, did not recompute any hash, and ran no Lean or Lake. The hashes below are copied from the packet and were not checked against the source index. I could not confirm which of the 172 listed theorems fall in this partition, so that check is passed to integration. Declarations are referenced by name; I give no line numbers because I could not count lines reliably without tools.

## 1. Files

I inspected the full body of every file supplied. None was skipped.

| # | File | SHA256 as supplied | Status |
|---|---|---|---|
| 1 | ActualBinaryMatrixHC46A7WeightedPredecessor.lean | 775FFB87…FDEE2 | Inspected in full |
| 2 | ActualBinaryMatrixHC46A8AmbientAssembly.lean | BE845673…7067C | Inspected in full |
| 3 | ActualBinaryMatrixHC46A8AveragedAssembly.lean | 0C5D9127…CD9D5CF | Inspected in full |
| 4 | ActualBinaryMatrixHC46A8AveragedTransport.lean | 83191C84…F2642 | Inspected in full |
| 5 | ActualBinaryMatrixHC46A8Endpoint.lean | 61387FFD…7E4FE9DEC9A555FA252A209B82C44EFB98374 — no: 61387FFD…3B3C3B4F7E | Inspected in full |
| 6 | ActualBinaryMatrixHC46A8EnergyNaturality.lean | 7B51AC35…98374 | Inspected in full |
| 7 | ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean | B15889A3…B6361 | Inspected in full |
| 8 | ActualBinaryMatrixHC46A8PairAssembly.lean | 15DED6AB…F39EB | Inspected in full |
| 9 | ActualBinaryMatrixHC46A9AmbientFiber.lean | 024850F6…6F9 | Inspected in full |
| 10 | ActualBinaryMatrixHC46A9AmbientReindex.lean | 5B4958CE…E8A2BE | Inspected in full |
| 11 | ActualBinaryMatrixHC46A9InitialGraph.lean | BF06040F…0A903 | Inspected in full |
| 12 | ActualBinaryMatrixHC46ActualFibreEvaluation.lean | 1136FA2B…81F08 | Inspected in full |
| 13 | ActualBinaryMatrixHC46ActualFibreModel.lean | 1359592B…79469 | Inspected in full |
| 14 | ActualBinaryMatrixHC46BooleanGlobalness.lean | A6FB4CA9…C2374 | Inspected in full |
| 15 | ActualBinaryMatrixHC46CommonA16.lean | 5B200903…542052 | Inspected in full |
| 16 | ActualBinaryMatrixHC46DR6Convolution.lean | CDDF6433…EE5D7 | Inspected in full |

Correction to row 5: the Endpoint hash as supplied is `61387FFD44E802D95E4FC0B21F4FC2DC4B9C6B833A9DB6112F3821B3C3B4F7E`.

## 2. Main checks

**Path from the A8 endpoint to A9** (`a8_output_q_le_actual_predecessor_sum` ← `a8_actual_coordinate_q_le_final_sum`):
- **Exhaustive, no double counting.** The output pair-shares cover every output pair (`hexhaust`, which relies on `a7_pair_shares_exhaust` from another partition). Output pairs paired with their complements are matched one-to-one with the hybrid complement sigma-type (`a8NestedPairEquiv`). Those are matched one-to-one with all geometric pairs (`a8T2AllPairEquiv`): A2 = R ⊔ C′ and B2 = H′ ⊓ K are recovered uniquely. Geometric pairs are in turn matched one-to-one with ambient final pairs (`a8AmbientFinalPairEquiv`, through the two `incidence_iff` lemmas). So each final predecessor is counted exactly once.
- **Direction and averaging.** The inequality runs LHS ≤ RHS, and the RHS is non-negative. The square stays inside both the T and S0 averages: `hpoint` is applied pointwise, then the T-translation is removed with `Equiv.addRight` for each fixed S0. No Jensen step merges the two averages, and the `card ΩS` factor cancels exactly.
- **Cube loss** (`a8_complex_normalized_mean_cube`). Pointwise |Σ|² ≤ m·Σ|·|², then E² ≤ m²(Σe)² ≤ m³Σe². The complement count is cubed exactly once, in the correct direction.
- **Exponent budget** (`a8_supported_graph_charge`). When cost ≤ D, the complement cost satisfies u = dim c + codim h ≤ cost ≤ D, so 3·k·u ≤ 3Dk ≤ 6Dk. When cost > D, the energy is zero by `a8_actual_energy_zero_outside_supported_window`. The stated budget 2^(6Dk) is therefore valid with a factor-2 slack in the exponent (see N3).
- **Selector consistency.** The tuple order of `t2RightSelected` is used the same way in `a8_complex_t2_pair_reindex` (disjoint, cover, intersection, top) and in both branches of `a8_fixed_complement_t2_typed_fourier`. The fields of `a7T2ComplementPair` (`p.2.1` through `p.2.2.2.2`) are also used consistently.

**Bridge from A8 to A9.** The endpoint's indicator `A′ ⊓ (range X).comap C.mkQ = C ∧ B′ ⊔ (ker X).map H.subtype = H` is exactly `a9AmbientA8SideConditions` with A0 = C and B0 = H. `a9Ambient_A8_sideConditions_iff_rank_preservation` is proved in both directions. The energy expression in `a9AmbientA8Energy` is the same expression as `finalEnergy` in the endpoint. The A9 coarse charge needs a + b + k ≤ D. The complementary case, a + b + k > D, gives zero energy by the support-window lemma in file 3. The two cases fit together, but the case split itself is not in this partition (see Integration).

**A7 and A9 counts.**
- `w6_actual_predecessor_frequency_fiber_card` is universal over X and Z, with l = rank Z. It has no fiber-count premise. The forward map uses the derived rank (`w6_precedes_actual_carrier_frequency_rank`); the backward map re-derives `w6Precedes` from the block rank. The count is 2^(2kl).
- `a9_ambient_fiber_card` is exact: Gaussian[a,i] · Gaussian[b,j] · 2^(k(a−i)) · 2^(k(b−j)). The B0 count uses Gaussian symmetry and only compares numerical counts. The hypotheses i ≤ a and j ≤ b hold automatically on the carrier, so they are not vacuous.

**Vacuity and assumptions.** Every premise is satisfiable: support through D, rank equalities that define k and l, and injectivity/surjectivity factorizations that `w6_matrix_rank_factorization` constructs. I found no `sorry`, no new `axiom`, and no hypothesis that assumes its own conclusion.

**Unrestricted-η HC46 and real-q A22 (as visible here).** In `exactPR_to_raw_normSqGlobal`, η is arbitrary; η ≥ 0 is derived from the Boolean mean rather than assumed. The empty-fibre case is handled. No hHC premise appears in any file of this partition. No real-q A22 declaration is in this partition, so that audit belongs to another partition.

## 3. Findings

| ID | Severity | Location | Finding |
|---|---|---|---|
| N1 | Low | `A8Endpoint.a8_output_q_le_actual_predecessor_sum` | The premise `_horder : a6Order t ≤ D` is never used. The theorem is sound, but it narrows its own applicability, so the consumer must still discharge it. The docstring says "no support-window premise", yet `hsupport` is required; I read this as referring to per-pair windows, and the wording should say so. |
| N2 | Info | Module docstrings of `A8AveragedAssembly` and `A8AveragedTransport` | These comments claim the work was "accepted with notes against frozen run 46/56". Those claims are unverifiable here, and I did not treat them as evidence of acceptance. |
| N3 | Info | `a8_supported_graph_charge` | The proof establishes 2^(3Dk); the statement charges 2^(6Dk). This is conservative and correct, but integration should confirm that 6Dk is the manuscript's intended budget and not a misreading. |
| N4 | Low | `A9AmbientReindex` (`a9AmbientA8Energy`), `CommonA16` (`complexRealDot`), `A8Endpoint` (`finalEnergy`) | Public theorem statements mention private definitions. This is sound, but downstream files can only consume these theorems by definitional unfolding. |
| N5 | Info | `A7WeightedPredecessor` | `end` closes the `noncomputable section` before the final five declarations, so the local `Classical`/`ofFinite` instances no longer apply there; the private Fintype instance is used instead. Card is unaffected because Fintype is a subsingleton. Two declarations use `/-` instead of `/--`, so their documentation is lost. |
| N6 | Info | A9 files | `F`, `V` and `W` are public abbrevs, and a generic `Fintype (P →ₗ Q)` instance is global. Both are hygiene risks only. |
| N7 | Info | Several files | Uses of `backward.isDefEq.respectTransparency false`, `with_unfolding_all`, and raised `maxHeartbeats` affect elaboration only; the kernel re-checks the proofs. |
| N8 | Info | `A9InitialGraph` vs `A9AmbientFiber` | The two files use different B0 conventions: B0 ⊆ B with dimension j, versus B ⊆ B0 with codimension j. The counts agree. `A9InitialGraph` itself says it is not charged to `a7HybridQ`, so integration must confirm the consumer uses `A9AmbientFiber`/`Reindex`. |
| N9 | Info | `DR6Convolution` | This module is explicitly staged: coverage, the 2^(r²) decomposition bound, Parseval/convolution, and 2D support. DR6 itself is not proved here, and the docstring correctly says so. |
| N10 | Info | `A8AveragedTransport` | `a8_fixed_base_complement_cube` and `a8_base_average_complement_cube` are private and unused (dead code). |

## 4. Questions left open for integration

1. Confirm that this packet's files and declarations match the exact list of 172 theorems and the 319-file source closure. I could not read the source index.
2. Check the definitions from other partitions that this partition relies on: `t2RightSelected`, `a7T2ComplementPair`, `a7_t2_complement_card_le`, `a7_pair_shares_exhaust`, `manuscript_A1_complex`, `filteredCarrierFunction_support_drop`, `filteredCarrierFunction_rankProjection_zero_of_below_carrier`, `a7_a9_multiplicity_le`, `w6PredecessorDescendedEnd`, `mixedCoordinateDerivativeChain_complex_orthogonal`, `PseudorandomExact`, and `actualGlobal_A15_complex_fixedLine`.
3. Check that the selected consumer performs the a + b + k ≤ D versus > D case split when it combines the A8 endpoint with `a9Ambient_fixed_fiber_coarse_charge`, and that it can discharge `_horder`.
4. Audit the real-q A22 path and the full HC46 chain without hHC; neither is present in this partition.
5. External boundaries: Init, Mathlib and Batteries are trusted at their pinned versions and were not re-reviewed.
6. Still open and outside this review: Spectral47; the source/star/robust8S/numericNO/encoded-reduction/runtime/learning items; the upstream bridges; and the manuscript, render and novelty gates.
