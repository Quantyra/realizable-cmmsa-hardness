# Partition 4/9 review: `ActualBinaryMatrixHC46A7Transfer.lean` (Full89 A22/HC46 milestone)

**Verdict: GO-WITH-NOTES** for this file only. This is not a verdict on the whole campaign or the whole milestone.

I read every declaration body in the file and skipped none. I did not run Lean, Lake or any other tool, so I am relying on the reported build for kernel acceptance. I did not check the SHA256, and I did not see the 172-theorem list because it sits behind the source index, which I could not open without tools. So I cannot say which declarations here are among the 172 roots. Line numbers were not supplied, so I cite findings by declaration name.

## Files

| File | Status |
|---|---|
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7Transfer.lean` (stated SHA 32EB…FD) | Inspected, all bodies read |

## Text-level trust scan
- The file contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` or `opaque` escape hatch.
- It does use `decide`, which the kernel evaluates. It also turns on `Classical.propDecidable` and `Fintype.ofFinite` as local instances, and raises `maxHeartbeats` to 1,500,000.
- There is no `hHC` premise anywhere in the file, and no eta or real-q parameter. So unrestricted-eta HC46 and real-q A22 are **not addressed in this partition** and are left to integration.

## What the file proves
I checked direction, quantifiers and assumptions by hand.

**Unconditional:**
- **Degree 0:** `manuscript_A7_degree_zero`, for every `n` and `d`, holds with equality. The support is through 0, so the input is constant, the fourth moment equals (L2)², and that equals Q.
- **Degree 1:** `a7_degree_one_fourth_bound` gives fourth moment ≤ 2^100·Q. The mixed sum is discharged by `a7_mixed_sum_degree_one`: every order above 1 has zero fourth moment, and the order-1 part goes through `a7_saturated_all_pairs_fourth_sum_le`, which charges each carrier once through injective parents.
- **Lower bound on Q:** `a7_q_ge_l2` gives (L2)² ≤ Q for every input. The direction is correct for its use in `a7_positive_of_mixed_bound`, where the coefficient is positive.
- **Order-D part, every D:** `a7_saturated_weighted_all_pairs_le` bounds it.
- **Exact factor-1 identities:** `a7_nested_hybrid_share_eq`, `a7_coordinate_pair_avg_eq_original` and `a7_mixed_coordinate_pair_avg_eq_original`.
- **Scaling:** `a7_hybridQ_smul` gives Q(c·f) = |c|⁴·Q(f), which is consistent with Q having degree 4.

**Conditional, and the docstrings say so:**
- `a7_positive_of_mixed_bound` needs `hS`.
- `a7_mixed_sum_of_shares` and `a7_positive_of_overlapping_shares` need `e`, `hfourth` and `hshare`.
- `a7_a9_preceding_output_sum_le` and `..._graph_charge` need a parent family satisfying `hprec` and `hsel`.

None of these is stated as a universal claim.

## Numerical checks (all pass)

| Declaration | Condition | Why it holds |
|---|---|---|
| `a7_l2_slack` | 162 ≤ 2⁸, and 8 + 6D² ≤ 100D² for D ≥ 1 | direct |
| `a7_terminal_factor` | 162·(2⁻⁹⁴ + 2⁻³⁰) ≈ 1.5·10⁻⁷ < 1, and both exponents decrease in D | direct |
| `a7_triple_exponent_fits` | 24Dt + 100(D−t)² ≤ 100D² + 1 − 31D | reduces to 176Dt − 100t² − 31D + 1 ≥ 76Dt − 31D + 1 > 0, using t ≤ D |
| `a7_triple_share_exponent_fits` | same with +9Dt | ≥ 67Dt − 31D + 1 > 0 |
| `a7_saturated_pool_exponent_fits` | 30D² + 1 ≤ 100D² + 1 − 31D | 70D² ≥ 31D for D ≥ 1 |
| `a7_a9_multiplicity_le` | (i+k)(a−i) + (j+k)(b−j) ≤ 2Dt, and the 4 or 16 factors fit | needs Dt ≥ 2 or Dt ≥ 4, which the proof derives in each branch |
| `a7_output_zero_share_le_original_component` | 4k(D−t) ≤ 9Dt | k ≤ t |
| `decide` lemmas | 2¹²⁹ < [24 choose 12]₂ and 2³⁶⁰ < [38 choose 19]₂ | each of the k factors of the Gaussian binomial is ≥ 2^(n−k), so the values are ≥ 2¹⁴⁴ and ≥ 2³⁶¹ |

## Findings

1. **Medium (integration) — the file header.** The general positive-degree A7 is **not proved in this file**. The header and the docstring of `a7_degree_one_fourth_bound` hand final A7 to `ActualBinaryMatrixHC46A11WeightedAggregate`, which is not in this partition. Within this file, only degrees 0 and 1 are unconditional.

2. **Medium (integration, overlap multiplicity) — `a7_mixed_coordinate_pair_avg_eq_original` and `a7_coordinate_pair_avg_eq_original`.** Each output pair maps to one original pair above (C, H) with factor 1. But the same original pair sits above many carriers and triples. Whoever discharges `hS` must pay that multiplicity: the A9 count 2^(3D(i+j+k)) and the A8 graph cost, which `a7_a8_a9_exponent_fits` shows fit inside the allowance. The file proves those counts but does not assemble the overlap. Integration should confirm that A11 does.

3. **Low (near-vacuity) — `a7_a9_preceding_output_sum_le` and `a7_a9_preceding_output_graph_charge`.** The only witness of the hypothesis family is the constant zero parent (`a7_a9_zero_parent_family_le`), which ignores the graphs. Meanwhile `a9ThetaParent_not_both` and `a9FinalParent_not_both` prove that the natural rank-k datum parent cannot satisfy `hprec ∧ hsel` against a rank-k final when k > 0. Any downstream consumer that charges through these with real datum parents would be vacuous. Integration should check A11's use.

4. **Low (documentation) — header and `a7_degree_one_fourth_bound`.** The docstrings say "accepted with notes at frozen run 56". That is an acceptance claim written into the source. It is not evidence, and I have not counted it.

5. **Info — refutation lemmas.** `a7_middle_grassmannian_exceeds_share_slack`, `a7_rank38_character_q_exceeds_order_one`, `a7OrderOne_output_q_exceeds_component` and `a7OrderOne_remaining_output_exceeds_leftover` show, on a concrete 40×40 example with D = 40, that charging each output to a single original component fails. They are sound diagnostics. They also confirm that `e` and `hshare` cannot be discharged per component.

6. **Info — `a7_one_hybrid_filter_sq_le_component`.** It holds for any real between 0 and the full energy. The name suggests more than it proves, but it is harmless.

7. **Info — `decide` with a local classical instance.** These lemmas only pass if a computable `Nat` order instance is chosen over the local `Classical.propDecidable`. I take the reported zero-error build as evidence that it was, and my own numbers above confirm the claims are true.

## Cross-partition questions for integration
This file depends on statements from other files that I could not see:
- `manuscript_A6`: it must have the form fourth/162 ≤ 2^(6D²)·(L2)² + S.
- `a6_mixed_zero_of_order_gt`, `a6_reconstruct_forward`, `a6_mixed_fourth_output`
- `typedW6FilteredCarrierFunction_le_two`: the weight must be 2^(6·D·rank).
- `actualW6Derivative_energy_sq_le_degree_predecessorFourierEnergy`, `w6PredecessorFourierEnergy_le_uniformMean`, `actualW6Derivative_energy_eq_zero_of_rank_gt`
- `w6_card_rank_k_predecessors`, `w6_gaussian_le_four_pow`, `w6_card_grass`
- `a9_inducing_card`, `a9_initial_datum_card`, `a9InitialMap_*`
- `manuscript_A1_complex`, `actualDerivativeCoordinate_nestedFilter`
- `t2_left_to_right`, `t2_right_to_left`, `t2_rejected_right`
- `complex_carrier_parseval`, `actual_affine_derivative_energy_eq_selected_fourier_mass`
- `filteredCarrierFunction_support_drop`, `carrierFourier_support_iff_coordinate`

Beyond those, the milestone questions for HC46, A22 and the selected consumer still need answers from other partitions:
- whether A11 discharges `hS` for every D, including the overlap point in finding 2;
- the unrestricted-eta and real-q statements;
- the absence of an `hHC` premise anywhere in the consumer chain.

The external Init/Mathlib/Batteries code is trusted as library code and was not re-reviewed here.
