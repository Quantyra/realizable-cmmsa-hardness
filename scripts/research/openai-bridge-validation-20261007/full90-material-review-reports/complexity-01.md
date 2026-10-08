# Complexity review, packet 1 of 5: the material export, the four critical re-reads, the new bodies here and the 23 Complexitylib boundary files

**Verdict for this packet: GO-WITH-NOTES.** This verdict covers packet 1 only. It is not material-review completion, material readiness, acceptance, or a verdict on the whole manuscript.

- **Inspection:** I read all 32 complete files in this packet in full and skipped none.
- **No tools:** I ran no Lean or Lake and recomputed no hashes. Each file header's hash matches its pin, but only as a label.
- **What is taken on receipt:** whether the files compile and their axiom profiles come from the supplied native receipts.
- **Hand checks:** the arithmetic, quantifier and proof-direction checks below were done by hand.
- **Library trust:** Init, Mathlib and Batteries are trusted at their pinned versions and were not reviewed.
- **Complexitylib:** this is the first time it has been reviewed. I did not treat it as already reviewed.

## 1. File coverage

| # | File | Status | Pinned as consumed? |
|---|---|---|---|
| 1 | ActualSelectedComplementHC46OriginalApplication | Inspected. This is the changed file and contains the export. | yes |
| 2 | ActualSelectedComplementAnalyticMoment | Inspected (critical re-read) | yes |
| 3 | ActualSelectedComplementAppendMoment | Inspected (critical re-read) | yes |
| 4 | ActualBinaryMatrixHC46OriginalExactInhabitant | Inspected (critical re-read) | yes |
| 5 | ActualLeafLabelRankImageAlignment | Inspected (critical re-read) | yes |
| 6 | ActualAffineRestrictionComposition | Inspected (new) | **no**: compile evidence only |
| 7 | ActualAppendFourierCrossLevelOrthogonality | Inspected (new) | yes |
| 8 | ActualBinaryGrassmannSamplingBounds | Inspected (new) | yes; which constants are reached is not listed |
| 9 | ActualBinaryMatrixHC46A11WeightedAggregateChecks | Inspected (new). Harness only, no proofs. | no |
| 10–32 | Complexitylib: Cheeger, EdgeExpansion, Expander, ExpanderExists, ExpanderMerge, ExpanderPad, ExpanderRandom, FamilyFin, MergeGen, Mixing, NumEnc, PermArith, PermCount, PermGraph, Power, RegularGraph, TowerFin, Union, Walk, WalkPath, ZigZag, ZigZagBaseExists, ZigZagTower | All 23 inspected | 4 are direct boundaries |

## 2. The export: `selected_actual_material_moment_bound_original`

**Conclusion.** The statement matches `selected_actual_material_moment_bound` exactly:
- the same `let` bindings for h, J, c, s, n, Cc, Tc and fc;
- the same `∃ k q, k = 2^q ∧ 4m ≤ k ∧ k < 8m ∧ matchingStarMass(A.1, transported C/T, f) ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a) ∧ matchingCenterMass(A.1, …) = Grassmann center fraction(Cc, fc)`.

The proof is a single `exact`, so the kernel has confirmed the two types are definitionally equal.

**Premises removed.** Only `hHC`. It is filled by `original_HC46_exact : HC46ExactContract`, which is the same constant defined in AnalyticMoment. There is no import cycle: the export sits downstream of OriginalExactInhabitant.

**Premises kept.** These are explicit and unchanged:
- `hsel`, `hA`, and `hrd : r < leafT + leafK`;
- `e` with `he : 0 ≤ e`;
- `hfail`: every zoom with `q + codim P.W = r` exactly and nonempty card has agreement on `selectedCoordinateLeafTable I copies U A T` at most e;
- `hSpectral : Spectral47ExactContract sourceHeightCutoff`;
- `a` with `ha : 0 < a`.

**No weaker substitute.** The export calls the material theorem directly. It does not route through `selected_leaf_HC46_original`, which would not even typecheck here (it needs `LeafTable (2*h)` where this needs `c+s`). The material theorem instead uses `hEven := hsplit` internally.

**Same objects throughout.** The same I, copies, U, A, C, T and f give Cc, Tc and fc. That one Tc is used in `hfail`, in the PR premise and in the moment, and the center identity is stated for the same Cc and fc.

**Effect on earlier open items.**
- The 173-root native trace now covers `selected_actual_material_moment_bound` and AppendMoment, and both are pinned as consumed. That resolves prior R1-m (no export and no profile existed) and R10 (AppendMoment not consumed).
- What remains is the explicit conditional premises above.

**Re-checks on the four critical bodies** (all by hand):
- **AppendMoment:**
  - c + m·s + 2h ≤ 2h(m+1) + 2h ≤ 2h² < 2J, using m+2 ≤ h and h² < J.
  - The rank-loss factor is N0·2^(2h−1)/2^(2J) ≤ 1/2.
- **Inhabitant:**
  - 200i²p² + (10i² + 500i²p)(p/2 − 1) ≤ 455i²p².
  - δ = min(η, 1); the δ = 0 case is handled.
  - η ≥ 0 is derived, not assumed.
- **LeafLabel:** leafMatchBit equals matchingLeafSet as functions; the failed-zoom premise gives PR at 2e when r < d.
- **AnalyticMoment:**
  - The low/high split is exact Fourier reconstruction.
  - Hölder is applied with p/m ≥ 1, and the exponent window is 4m ≤ k < 8m.
  - HC46 is applied at every level i ≤ r, with `hEven := hsplit` and 4 ≤ k.

## 3. Findings: project files

| ID | Severity | Declaration | Finding / disposition |
|---|---|---|---|
| P1 | Low (documentation) | OriginalApplication block comment | It says "This candidate has not been compiled or independently accepted." The first half is stale against the native receipts. The "not accepted" half remains true. The AnalyticMoment header's "contracts… not claims proved locally" is now stale for HC46. |
| P2 | **Medium (fidelity; gate stays OPEN)** | `Spectral47ExactContract` | **Unverified hand derivation**, assuming the convention `pairing = Σ Y_ij M_ij` and Parseval-normalised `fourierCoeff`:<br>1. `basisInv` makes F̂ constant on column-space orbits.<br>2. `appendAverage χ_Z` keeps only frequencies of the form `[Y\|0]` (proved in file 7).<br>3. So for each orbit, the LHS/RHS ratio is ∏_{j<i}(2^c − 2^j)/(2^{c+s} − 2^j) ≤ 2^{−is} ≤ 2^{−i(s−1)}.<br>4. This uses none of ρ, h, n, `hHeight`, or the 3·2^{i−n} term.<br>Two consequences: `hSpectral` is probably cheap to discharge in Lean, and the encoded contract may be weaker than, or different from, manuscript Spectral 4.7. The contract is **not proved in Lean**. Spectral47 stays open, and its fidelity must be checked against the manuscript before it is called "Spectral 4.7". |
| P3 | Medium (numeric NO; OPEN) | `selected_actual_analytic_rhs` | m ≥ 256 forces k ≥ 1024. Each low level contributes 2^(500i²k)·(2e)^((k−2)/k) inside an m-th power. For any r ≥ 1, a nontrivial bound needs e of roughly 2^(−5·10^5) or smaller. r is a free parameter with r < c+s; r = 0 leaves only the mean. Whether any choice is useful, and whether `hfail` can hold with such an e, has not been shown. |
| P4 | Info (satisfiability) | export premises | The bound is only as meaningful as its premises. `hsel` and `hfail` are not shown satisfiable here. If agreement ≤ 1 always holds (agreement is defined in another packet), then e = 1 satisfies `hfail` trivially and the conclusion is weak. |
| P5 | Info | AffineRestrictionComposition | Same-base fibre intersection, order subadditivity (dim of the sup plus codim of the inf) and the raw-to-actual bridge are all correct. The file is unconsumed, so it has compile evidence only and no profile. |
| P6 | Info | AppendFourierCrossLevelOrthogonality | Character factorisation, the block-zero filter and cross-rank orthogonality are correct. This is the lemma that underlies `appendHighLevel_energy_eq_sum`. |
| P7 | Info | BinaryGrassmannSamplingBounds | Checked by hand: frame ≥ 1/2; the 127/128 window (2^(b+7) ≤ 2^(n−r)); the per-factor pair-product inequality (AM-GM, 2·2^(n−r) ≤ 2^(n−2r) + 2^n); the Chebyshev constant 625·128/127 ≤ 630; the bad window [19/20, 21/20] lying inside the 1/25 relative-deviation event. Only some constants are reached (probably `gaussian_pos`, via the center lemma). The rest have compile evidence only. |
| P8 | Info | A11WeightedAggregateChecks | `#check` and `#print axioms` lines only, and their outputs were not supplied. It provides no evidence beyond the fresh 173-root output. |

## 4. Complexitylib boundary review (23 files)

**Soundness of the mathematics read: no defect found.** I checked these by hand:
- **RegularGraph:** `SpectralBound` is a two-sided squared operator-norm bound on mean-zero functions. Contraction and t-step iteration hold.
- **Mixing:** the mixing lemma in squared form.
- **EdgeExpansion:** (1−λ)·d·|S||Sᶜ|/n ≤ e(S, Sᶜ).
- **Union:** the bound (d_G + d_H·λ)/(d_G + d_H), with the cross term handled without square roots.
- **Cheeger:** co-area peeling, Cauchy–Schwarz giving h²d‖φ‖² ≤ Dirichlet, a median split, and the lazy-walk bound 1 − h²/4 via the PSD form.
- **Permutation construction:**
  - PermGraph: h = 1/(2cD).
  - PermCount: the count bound is descFactorial·(n−k)!.
  - PermArith: 2^20·3^310 ≤ 2^540 and 3^31 ≤ 2^52.
  - ExpanderRandom: the union bound through the geometric slack.
  - ExpanderExists: 30 permutations give degree 60, h = 1/600, the lazy graph has degree 120, and λ = 1 − 1/1.44·10^6.
- **Power, Walk, WalkPath:** reversal is an involution, and the power graph has bound λ^t.
- **ZigZag:** RVW bound λ_G + λ_H + λ_H², with the spectral bound obtained by polarisation.
- **ZigZagTower:** the bound recurs exactly: 4/25 + 1/5 + 1/25 = 2/5.
- **ZigZagBaseExists:** the base is d^(4m) vertices with bound λ^m ≤ 1/5.
- **MergeGen and ExpanderMerge:**
  - Balanced fibres mean at most one padding loop per vertex.
  - The merged bound is √(λ² + (1−λ²)/(2m) + 1/m), and it needs N ≥ 2n.
- **FamilyFin:** with the minimum width 3, 0.16 + 0.14 + 1/3 ≈ 0.633 ≤ 0.64. Padding then gives √(1 − 27/(25W)) < 1.
- **NumEnc:** encode and decode round-trip.

**Representations:**
- Multigraphs are given by rotation-map involutions, with self-loops and parallel darts allowed.
- `relabel`, `relabelV` and `toFinForm` preserve the step operator.
- `padLoops` and merging degrade λ by explicit amounts.
- Empty vertex sets satisfy any λ (`spectralBound_of_isEmpty`), and `famRot 0 = id`.
- `expanderize` depends on the chosen NumEnc numbering.

| ID | Severity | Finding |
|---|---|---|
| X1 | **Medium (computational claims)** | **None of the 23 files proves a computational or runtime bound.** The words "explicit", "an algorithm can read" and "polynomial" appear only in docstrings. `randExpander`, `algFamily`, `famRot` and `famRotVal` are all `noncomputable` and rest on `Classical.choose`. `fifthExp` is an arbitrary witness, at least ln5/−ln(1 − 1/1.44·10^6) ≈ 2.3·10^6 and with no upper bound, so `algFamily`'s degree is about 120^(≥2.3·10^6)·… and is not a known numeral. These files must not be cited for encoded-reduction or runtime claims; those gates stay OPEN. |
| X2 | Medium (sampling) | ExpanderRandom proves **existence only**. The geometric step gives bad tuples ≤ (1 − 2^−n)·(n!)^30, so a uniform random tuple is good with probability at least 2^−n, not with high probability. PermGraph's "a random tuple works" must not be read as a sampler guarantee. |
| X3 | Low (constants) | The spectral gaps are positive but tiny or unspecified: `randLam` = 1 − 6.9·10^−7, and `famLam` = √(1 − 27/(25(2d⁴+1))) with an astronomically large d. Any downstream parameter that depends on the gap inherits constants with no explicit bound. |
| X4 | Info | The Expander.lean docstring says the library has no Cheeger inequality or zig-zag product. That is stale and contradicted by Cheeger.lean and ZigZag.lean. |
| X5 | Info (the interface is inhabited) | `ExpanderFamily` is genuinely inhabited by `randExpander` and `algFamily` within the reviewed sources, assuming the native compile. So an `ExpanderFamily` parameter would not be vacuous, but it carries no explicit constants or runtime. |

## 5. Questions for integration

1. **Which project modules reach Complexitylib, and how?** In particular, does `ActualOccurrenceAllocation.Instance`, which appears in the type of the material export, take an `ExpanderFamily` as a parameter, or use `algFamily` / `randExpander`? Which of the 2738 boundary constants belong to these 23 files?
2. **Definitions in other packets:** `selected_spectral_parameters` (`hcReal`, `hsReal`, `hcutFloor`), `analyticSourceHeightFloor`, `selector_spec`, `blocks` / `numerator_lt_blocks`, `leafT` / `leafK`, `matchingStarMass_cast_le_twice_actualAppendRankImageMoment`, `matchingStar/CenterMass_actual_coordinate`, `matrix_grassmann_identity`, `alpha_bounds`, `actualLeafIndicator_mul_right_eq`, `failed_zoom_gives_nominal_pseudorandom`, the range of `agreement` (relevant to P4), and the `fourierCoeff` / `pairing` normalisation (relevant to P2).
3. **Spectral 4.7:** confirm its manuscript statement against P2, and decide whether `hSpectral` should be discharged in Lean.
4. **Still open:** Spectral47 (proof and fidelity); numeric NO / useful e; the source/star/robust8S, encoded-reduction, runtime and learning gates; upstream builds and bridges; warning disposition (zero owned warnings is not zero total warnings); a fresh checkout; manuscript fidelity, rendering, novelty and citations; the final providers.

## 6. Safe conditional claim

This rests on the pinned kernel, Init, Mathlib and Batteries trust, the native receipts (173 roots including the export, with standard profiles; 319 sources; seven zero exits), and these 32 bodies.

> For every material I, copies, U, A, C, T and f, and parameters satisfying `hsel`, `hA`, `r < c+s`, `0 ≤ e`, `hfail(e)`, `Spectral47ExactContract(cutoff)` and `a > 0`, there is a dyadic k with 4m ≤ k < 8m such that:
> - the transported matching-star mass is at most 2·`selected_actual_analytic_rhs`(Cc, Tc, fc, r, k, 2e, a);
> - the matching-center mass equals the exact Grassmann center fraction.
>
> HC46 is discharged internally by `original_HC46_exact`.

Not claimed: Spectral47, numeric usefulness, any Complexitylib-based runtime or explicitness, acceptance, or any whole-manuscript verdict.
