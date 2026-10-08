# Non-claims review: Full89, partition 5 of 9 (A22/HC46 selected-consumer milestone)

**Verdict for this partition: GO-WITH-NOTES.** I found no blocking defect in the 16 files supplied here. All of them were read in full. This covers partition 5 only and is not a verdict on the whole campaign. The open items you listed stay open: Spectral47, source/star/robust8S/numericNO, encoded reduction, runtime/learning, upstream bridges, and the manuscript/render/novelty gates.

**Limits of this review:**
- I had no tools, so I did not open the source index, recompute the SHA256 hashes, or check that anything compiles.
- Your statement of the native gates (seven zero exits, 172 axiom profiles, 7251-node trace with nothing unresolved) is taken as given.
- Without tools I couldn't compute exact line numbers. Findings are tied to declaration names instead, which identify the spot exactly.

## File status (all 16 inspected; nothing skipped)

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46A7WeightedPredecessor.lean | Inspected in full |
| 2 | ActualBinaryMatrixHC46A8AmbientAssembly.lean | Inspected in full |
| 3 | ActualBinaryMatrixHC46A8AveragedAssembly.lean | Inspected in full |
| 4 | ActualBinaryMatrixHC46A8AveragedTransport.lean | Inspected in full |
| 5 | ActualBinaryMatrixHC46A8Endpoint.lean | Inspected in full |
| 6 | ActualBinaryMatrixHC46A8EnergyNaturality.lean | Inspected in full |
| 7 | ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean | Inspected in full |
| 8 | ActualBinaryMatrixHC46A8PairAssembly.lean | Inspected in full |
| 9 | ActualBinaryMatrixHC46A9AmbientFiber.lean | Inspected in full |
| 10 | ActualBinaryMatrixHC46A9AmbientReindex.lean | Inspected in full |
| 11 | ActualBinaryMatrixHC46A9InitialGraph.lean | Inspected in full |
| 12 | ActualBinaryMatrixHC46ActualFibreEvaluation.lean | Inspected in full |
| 13 | ActualBinaryMatrixHC46ActualFibreModel.lean | Inspected in full |
| 14 | ActualBinaryMatrixHC46BooleanGlobalness.lean | Inspected in full |
| 15 | ActualBinaryMatrixHC46CommonA16.lean | Inspected in full |
| 16 | ActualBinaryMatrixHC46DR6Convolution.lean | Inspected in full |

## Results of the requested checks

**No added hHC premise.** None of the 16 files introduces an hHC-type hypothesis. The A8 chain's only analytic premise is `hsupport : ComplexFourierSupportedThrough D f`, with `f` an arbitrary complex function. That premise is satisfiable: the zero function meets it, and so does any `f` once D is at least the largest possible rank.

**Unrestricted eta (Boolean side).** In `exactPR_to_raw_normSqGlobal`, eta ≥ 0 is derived from the mean of the indicator, not assumed. Empty fibres are handled through that nonnegativity.

**Real-q / A22.** No real-q A22 statement appears in this partition. This partition only supplies the complex A8/A9 bound and its Boolean bridge; the A22 consumer is in another partition.

**Proof direction.** `a8_output_q_le_actual_predecessor_sum` gives E_T[Q(output)] ≤ 2^(6Dk) · Σ over final pairs of E_T[energy²]. That is the upper-bound direction the manuscript needs. The square stays inside both averages (T and S0), and there is no Jensen step that would merge them.

**Exponent bounds.**
- **Cubic loss** (`a8_complex_normalized_mean_cube`): (mean of |Σ_p|²)² ≤ m²(Σ e_p)² ≤ m³ Σ e_p². Correct.
- **Graph budget** (`a8_supported_graph_charge`): if cost ≤ D, then u+v ≤ D, so graph³ = 2^(3k(u+v)) ≤ 2^(3Dk) ≤ 2^(6Dk). If cost > D, the energy is 0 by `a8_actual_energy_zero_outside_supported_window`. Valid, with deliberate slack of a factor of 2 in the exponent.
- **Fixed-frequency predecessor fiber** (`w6_actual_predecessor_frequency_fiber_card`): exactly 2^(2·rank X·l). I checked this against the block form [[1+uc, up], [jc, jp]].
- **A9 ambient fiber** (`a9_ambient_fiber_card`): Gauss(a,i) · Gauss(b,j) · 2^(k(a−i)) · 2^(k(b−j)). The factors check out:
  - choosing A0: Gauss(a,i);
  - choosing B0: Gauss(b, b−j) = Gauss(b,j), proved by an annihilator bijection;
  - section maps into A/A0: dimension a−i;
  - extension maps out of B0/B: dimension b−j.

**Vacuity.**
- The side hypotheses `hA`/`hB` in the A8 transport are actually discharged at the use site, by `a8_nested_domain_contains` and `a8_nested_range_contained`.
- In the predecessor fiber equivalence, the backward map *proves* `w6Precedes`; it is not assumed.
- The A8 incidence conditions are shown equivalent to rank preservation (`a9Ambient_A8_sideConditions_iff_rank_preservation`), so the fiber is the genuine A8 predecessor set.

## Findings

**F1 — Medium (documentation; must not be treated as evidence).**
- *Where:* the module docstrings of A8AveragedAssembly and A8AveragedTransport.
- *What:* they state that results were "accepted with notes against frozen run 46" and "frozen run 56 (2026-10-06)".
- *Why it matters:* these are acceptance claims written into source comments. Nothing in this partition supports them, and they carry no proof weight. Integration must not count them as acceptance.

**F2 — Low–Medium (overclaim risk).**
- *Where:* A9InitialGraph.
- *What:* the module is a combinatorial model that is not connected to the actual A9 fiber:
  - `A9InitialDatum` puts B0 *inside* B, while the actual fiber (`A9AmbientB0`) has B0 *containing* B. The variance is opposite.
  - `a9_fiber_triple` uses C := ⊥ and K := ⊤, which is a degenerate placeholder.
  - The docstring of `a9InitialIndexed_K` admits that the rank statement "does not typecheck".
  - The module does say it does not charge anything to `a7HybridQ`.
- *Conclusion:* none of its counts may be cited as the A9 fiber count. The authoritative count is `a9_ambient_fiber_card` / `a9AmbientFiberEquiv`.

**F3 — Low (unused premise).**
- *Where:* `a8_output_q_le_actual_predecessor_sum`.
- *What:* it takes `_horder : a6Order t ≤ D` and never uses it.
- *Effect:* the bound stays true; callers just have to supply a premise the proof doesn't need. Integration should check that every consumer can actually provide it.

**F4 — Low (scope hygiene).**
- *Where:* A7WeightedPredecessor.
- *What:* an `end` right after `w6_actual_predecessor_graph_factorization` closes the `noncomputable section`. Everything after it loses the local `Classical.propDecidable` and `Fintype.ofFinite` instances, and two of those declarations use plain `/- -/` comments instead of `/-- -/` docstrings.
- *Effect:* no change to meaning (the needed instances are declared explicitly, and the build passes per your gates).
- *Also:* the docstring of `w6_card_a3_parameter_pair` still calls the fiber equivalence "still-needed", although it is proved later in the same file.

**F5 — Low (instance provenance; integration check).**
- *Where:* A8Endpoint.
- *What:* the file has no local `Classical.propDecidable`, yet its statement uses `if p.1.1 ⊓ … = C ∧ …`.
- *Check needed:* any downstream rewrite against an `ite` built with a different `Decidable` instance has to go through `Subsingleton`/`congr`.

**F6 — Low (private names inside public statements).**
- *Where:* `a9AmbientA8Energy` in A9AmbientReindex and `complexRealDot` in CommonA16.
- *What:* both are private, but appear in the statements of public theorems.
- *Effect:* consumers in other files cannot refer to them by name and must match by unfolding. This matters if the weighted A9 consumer restates these theorems.

**F7 — Low (dead or duplicate code; matters for counting roots and trust surface).**
- `a8_fixed_base_complement_cube` and `a8_base_average_complement_cube` (private, unused).
- `a8_two_base_actual_averaged_transport`, which the ambient version in A8AmbientAssembly duplicates.
- `a8_w6_domain_quotient_square`, duplicated by `a8_nested_final_domain_square`.
- The unused locals `hcanonicalC`/`hcanonicalH` in `a8_fixed_complement_t2_typed_fourier`, and the unused `hprob` in `dualSupVectorOutside_mean_le_two`.

**F8 — Low (fragile tactic).**
- *Where:* `a8_common_S0_filter_shift`.
- *What:* the proof relies on `try simp only … ; rw [hphase]` and a trailing `rfl`.
- *Effect:* it is correct as compiled, but brittle if the toolchain is upgraded.

**F9 — Informational (DR6 is not DR6).**
- *What:* DR6Convolution states explicitly that it does not prove DR6. It proves only:
  - the definitions of the ordinary selector and filter;
  - coverage: every additive triple is in F1 or F2 (`dr6_matrix_f1_or_f2_coverage`);
  - the decomposition count ≤ 2^(r²);
  - the Parseval and convolution identities;
  - the 2D support bound.
- *For whoever completes DR6:* `DR6F1Witness` leaves out the kernel-spanning condition, so F1 and F2 are not proved disjoint. The bound |conv| ≤ H_X + |O_X| needs each pair assigned to exactly one class (for example, F1 := ¬F2).

## Conditional facts vs. universal claims

- **Universal, unconditional:**
  - the fixed-frequency predecessor fiber count;
  - the A9 ambient fiber count (under hi/hj);
  - the equivalence between the A8 side conditions and rank preservation;
  - DR6 coverage;
  - the 2^(r²) decomposition bound.
- **Conditional on `hsupport`:** the A8 endpoint bound, plus the unused `_horder` from F3.
- **Conditional on `PseudorandomExact`:** the Boolean globalness bridges. The single A15 line step does *not* iterate the dyadic argument HC46 needs, as its own docstring says.
- **Conditional on `hfin : a + b + k ≤ D`:** the coarse A9 charge.

## Questions for integration (cross-partition and external boundary)

1. **Imported lemmas this partition depends on but does not prove** (their proofs are reviewed in other partitions):
   - A1 and the T1 collapse: `manuscript_A1_complex`, `t1TypedW6_collapse_parentFiber`, `t1CarrierPhase_general`.
   - T2 transfer: `t2_right_derivative_expansion`, `t2_right_to_left`.
   - A7 side: `a7_pair_shares_exhaust`, `a7_t2_complement_card_le`, `a7_a9_multiplicity_le`.
   - Support and rank-projection lemmas: `filteredCarrierFunction_support_drop`, `filteredCarrierFunction_rankProjection_zero_of_below_carrier`, `complexRankProjection_reconstruct_range_of_support`.
   - Carrier-coordinate lemmas: `carrierFrequency_rank`, `carrierFrequency_toLin`, `complexCarrierHybridFilter_coordinate`, `carrierCoordinate_affineMatrix`.
   - Grassmann counting: `w6_card_grass`, `w6Gaussian`.
   - Predecessor idempotent: `w6_predecessor_descended_idempotent`.
   - Affine fibre and dual-sup lemmas: `actualFibreLinearEquiv`, `ker_actualLeftMap`, `dualSupVector*`, `conditional_uniform_mean_le_two`, `binary_submodule_complement_card_eq`.
   - Pseudorandomness and A15: `pseudorandom_atMost_of_exact`, `raw_implies_actual`, `actualGlobal_A15_complex_fixedLine`.
   - Mixed derivative chain: `mixedCoordinateDerivativeChain_complex_orthogonal`, `commonMixedDerivativeChain_*`.
   - Fourier products: `complexFourierCoeff_mul_eq_convolution`, `complexFourierSupportedThrough_mul`.
2. **External library boundary:** all uses of Init, Mathlib, and Batteries are trusted as pinned library code (for example `LinearMap.trace_conj'`, `Subspace.dualAnnihilator_inj`, `Module.card_eq_pow_finrank`, `Matrix.rank_mul_eq_*_of_isUnit_det`). They were not re-reviewed here.
3. **The weighted A9 partition/charge consumer** that sums `a9Ambient_fixed_fiber_coarse_charge` over (i, j, k) and connects it to the A8 endpoint sum is not in this partition. It needs its own review, including the private-name matching from F6.
4. **The A22 real-q consumer** must instantiate the complex A8 endpoint with the Boolean or real input through `booleanIndicatorComplex` or an equivalent, without adding an hHC premise. This partition cannot check that.
5. **Hashes and root membership:** confirm that the 16 SHA256 values match the source index, and whether the duplicate or unused declarations in F7 are among the 172 roots.
