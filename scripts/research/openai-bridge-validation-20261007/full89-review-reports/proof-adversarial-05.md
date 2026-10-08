# Proof-adversarial review: Full89, partition 5 of 9

**Verdict: GO-WITH-NOTES, for this partition only.** This is not a verdict on the whole campaign or on HC46/A22 as a whole.

I read all 16 supplied files in full and skipped no bodies. I found no soundness defect. No declaration in these files has a vacuous or self-contradictory hypothesis set, an added hHC premise, a restriction on eta, or an inequality pointing the wrong way.

**Limits of this review:**
- I had no tools and executed no code. I did not re-run Lean, recompute the SHA256 hashes, or open the source index.
- I took kernel acceptance and axiom profiles from the native gate evidence you supplied.
- References are by declaration name. I couldn't compute line numbers without tooling.

## Files inspected (16 of 16 supplied)

| # | File | Status |
|---|---|---|
| 1 | `ActualBinaryMatrixHC46A7WeightedPredecessor.lean` | inspected |
| 2 | `ActualBinaryMatrixHC46A8AmbientAssembly.lean` | inspected |
| 3 | `ActualBinaryMatrixHC46A8AveragedAssembly.lean` | inspected |
| 4 | `ActualBinaryMatrixHC46A8AveragedTransport.lean` | inspected |
| 5 | `ActualBinaryMatrixHC46A8Endpoint.lean` | inspected |
| 6 | `ActualBinaryMatrixHC46A8EnergyNaturality.lean` | inspected |
| 7 | `ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean` | inspected |
| 8 | `ActualBinaryMatrixHC46A8PairAssembly.lean` | inspected |
| 9 | `ActualBinaryMatrixHC46A9AmbientFiber.lean` | inspected |
| 10 | `ActualBinaryMatrixHC46A9AmbientReindex.lean` | inspected |
| 11 | `ActualBinaryMatrixHC46A9InitialGraph.lean` | inspected |
| 12 | `ActualBinaryMatrixHC46ActualFibreEvaluation.lean` | inspected |
| 13 | `ActualBinaryMatrixHC46ActualFibreModel.lean` | inspected |
| 14 | `ActualBinaryMatrixHC46BooleanGlobalness.lean` | inspected |
| 15 | `ActualBinaryMatrixHC46CommonA16.lean` | inspected |
| 16 | `ActualBinaryMatrixHC46DR6Convolution.lean` | inspected |

The other ~154 files of the 170 are outside this partition and not covered here.

## Theorems that hold up

- **A7 predecessor fibre count** (`w6_actual_predecessor_frequency_fiber_card`): the count is exact, `card = 2^(2·rank X·l)` whenever `rank Z = l`.
  - The only hypothesis is `hZ`, which just names `l`, so the statement is effectively unconditional.
  - Not vacuous: the parameters `u = 0, c = 0` always give a fibre element.
  - Both directions of the equivalence check out. The rank-additivity `Y.rank = X.rank + (Y−X).rank` is derived in the backward map, not assumed.
  - The exponent goes from `2·l·k` to `2·k·l` by commutativity, which is correct.
- **A8 transport** (`a8_fixed_base_actual_energy_cube`, `a8_two_base_actual_averaged_transport`, `a8_ambient_two_base_actual_averaged_transport`):
  - The Cauchy chain `E ≤ mΣe` and then `E² ≤ m²(Σe)² ≤ m³Σe²` is correct, and the count is cubed only once.
  - The square stays inside the T and S0 averages; there is no Jensen step.
  - The S0 average is removed only by translating T, which is a bijection on the ambient Hom group. The `card ΩS` factor is kept and cancels correctly.
- **Supported-window charge** (`a8_supported_graph_charge`):
  - If `cost ≤ D`: the excess equals `dim p.1.1 + dim quotient`, which is at most cost and so at most D. That gives `3·k·excess ≤ 3Dk ≤ 6Dk`, a valid bound pointing the right way.
  - If `cost > D`: the energy is exactly 0 by `a8_actual_energy_zero_outside_supported_window`. Both of that lemma's sub-cases (`c ≤ D` with the rank comparison, and `c > D` where every rank projection vanishes) use the hypotheses in the correct direction.
- **A8 endpoint** (`a8_output_q_le_actual_predecessor_sum`):
  - The conditional sum's incidence conditions match `a9AmbientA8SideConditions` exactly, with `A=p.1.1, A0=C, B=p.2.1, B0=H`.
  - The constant is `k = finrank(range X)`.
- **A9 fixed-final fibre count** (`a9_ambient_fiber_card`):
  - The result is `[a,i]·[b,j]·2^{k(a−i)}·2^{k(b−j)}`.
  - Section lifts are maps `range Y → A/A0`; extensions are maps `B0/B → range Y`.
  - The B0 count comes from the actual nested quotient plus Gaussian symmetry.
  - Every fibre member provably satisfies the A8 side conditions, and the partition in `a9AmbientA8PartitionEquiv` is an exact bijection.
- **Unrestricted eta** (`exactPR_to_raw_normSqGlobal`): `eta ≥ 0` is derived from the Boolean mean rather than assumed. No restriction on eta appears anywhere in these files.

## Findings

1. **Low: section closed mid-file in `A7WeightedPredecessor`.**
   - An `end` right after `w6_actual_predecessor_graph_factorization` closes the `noncomputable section`.
   - So `w6_actual_predecessor_bottom_block_eq_frequency_matrix`, `…frequency_eq_of_coordinate_matrix_eq`, `w6_actual_block_displacement_rank`, the fibre equivalence and both card theorems sit outside it. They lose the local instances (`Classical.propDecidable`, `Fintype.ofFinite`) and `set_option autoImplicit false`.
   - The doc comments on two of these theorems have been demoted to plain `/- … -/` comments.
   - I checked by hand that every binder in those declarations is explicitly bound, so autoImplicit cannot have silently widened any statement. There is no soundness impact, but the file structure should be fixed.
2. **Low: unused premise `_horder : a6Order t ≤ D`** in `a8_output_q_le_actual_predecessor_sum`. It only narrows the theorem, it isn't contradictory, and it isn't used. The consumer still has to discharge it.
3. **Info: loose constant.** The proof actually gives `2^(3Dk)`, but the statement says `2^(6Dk)`. That is a valid and conservative bound. The A9 coarse charge inherits `6Dk`.
4. **Medium-for-integration: `A9InitialGraph` is not the fixed-final fibre.**
   - `A9InitialDatum` has no `induces` equation.
   - Its B0 is a j-dimensional subspace inside B, whereas the ambient fibre's B0 contains B with codimension j.
   - `a9_fiber_triple` is a degenerate triple (`C=⊥, K=⊤`).
   - Its counts agree with the real fibre only numerically. The file itself says it does not charge `a7HybridQ`.
   - The integration step must confirm that the consumer uses `a9_ambient_fiber_card` / `A9AmbientReindex` and never `a9_initial_datum_card`.
5. **Info: DR6 is staged, not proved.** `DR6Convolution` proves coverage (F1 or F2), the `2^(r²)` splitting count, the Parseval/convolution identities, and 2D support. It does **not** prove DR6, and it says so. Coverage is not a disjoint partition, so any later signed bound must split into ¬F2 / F2, which `dr6_matrix_f1_coverage` supports. The constants 81 and 162 in the docstring are not formalized.
6. **Info: unverifiable acceptance claims in comments.** The docstrings of A8AveragedAssembly and A8AveragedTransport say the work was "accepted with notes against frozen run 46/56". I did not treat these as evidence.
7. **Info: single-step result.** `BooleanGlobalness.exactPR_to_actual_A15_fixedLine` is one A15 step with loss `4·2^{4(k+1)}`. As its docstring says, it is not iterated.
8. **Info: phantom dimension arguments.** `a8NestedDomainEquiv` and `a8NestedRangeEquiv` instantiate external defs with `(n := 0)` / `(d := 0)`. The result types are fixed by the submodules and naturality is proved, so this is benign. It's worth confirming that those parameters really are phantom in the external definitions.

## Conditional versus universal

- **Universal (only hypotheses that fix parameters):** the A7 fibre card, the A9 fibre card (given `i ≤ a`, `j ≤ b`), and all the transport/naturality equalities.
- **Conditional:**
  - The A8 bounds are conditional on `ComplexFourierSupportedThrough D f` (plus `_horder` at the endpoint).
  - The A9 coarse charge is conditional on `a+b+k ≤ D`.
  - BooleanGlobalness is conditional on `PseudorandomExact`.
- **Not in this partition:**
  - The real-q A22 and unrestricted-eta HC46 statements, and the selected consumer, are not in these 16 files, so I can't judge them here. Nothing in this partition adds an hHC premise.

## Questions for cross-partition and external integration

1. These external lemmas need verification in their own partitions: `a7_t2_complement_card_le`, `a7_pair_shares_exhaust` (and the definitions of `a7PairShare` / `typedW6QComponent`), `manuscript_A1_complex`, `filteredCarrierFunction_support_drop`, `filteredCarrierFunction_rankProjection_zero_of_below_carrier`, `complexRankProjection_reconstruct_range_of_support`, `t2_right_derivative_expansion`, `t2_right_to_left`, `t1TypedW6_collapse_parentFiber`, `t1CarrierPhase_general`, `carrierFrequency_rank/_toLin`, `a7_a9_multiplicity_le` (I believe the claim `mult ≤ 2^{3D(i+j+k)}`, but haven't verified it), `w6_card_grass`, `w6PredecessorDescendedEnd`, `conditional_uniform_mean_le_two`, `dualSupVector*`, `mixedCoordinate*`/`commonMixedDerivativeChain_low_rank_zero`, `complexFourierSupportedThrough_mul`, `raw_implies_actual`, `actualGlobal_A15_complex_fixedLine`, `boolean_mean_le_of_exact`, `pseudorandom_atMost_of_exact`.
2. The consumer must swap the order of summation from the A8 endpoint, which fixes (C,H,X) and sums over final pairs, into `A9AmbientA8Source`, which fixes (A,B) and sums over (A0,B0,X). Its `k` and `D` must match the `6Dk` and `3D(i+j+k)` exponents, and the side conditions must be discharged.
3. The consumer must use the actual-fibre count and not the `A9InitialGraph` count (Finding 4).
4. The trust placed in Init/Mathlib/Batteries is a pinned-library assumption. This review did not re-check it.
