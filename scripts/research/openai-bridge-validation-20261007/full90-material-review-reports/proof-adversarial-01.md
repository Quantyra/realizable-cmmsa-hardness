# Proof-adversarial review, Full90 material-consumer packet 1/5

**Verdict for this packet only: GO-WITH-NOTES.** I read all 32 supplied file bodies in full and skipped none.

- **No blocking defect.** None of the 32 bodies has a soundness defect, a vacuous main statement, a reversed inequality, or a hidden extra premise.
- **The export is what it claims.** `selected_actual_material_moment_bound_original` removes exactly one premise, `hHC`. Its conclusion is the original material conclusion, and it is not the selected-leaf wrapper.
- **The material verdict is still INCOMPLETE across packets.** Several support bodies the proof depends on are in other packets (findings PA1‑07 and PA1‑08). This verdict says nothing about the whole manuscript.

**How I reviewed.** No tools, writes, Lean/Lake runs or subagents. I did not recompute any hash. Compile status, axiom profiles and trace identity come from the receipts you supplied. Library trust in Init, Mathlib and Batteries is explicit and was not reviewed. Findings cite declaration names, not line numbers.

## 1. Files

| # | File | Kind | Status |
|---|---|---|---|
| 1 | ActualSelectedComplementHC46OriginalApplication | changed | inspected |
| 2 | ActualSelectedComplementAnalyticMoment | critical re-read | inspected |
| 3 | ActualSelectedComplementAppendMoment | critical re-read | inspected |
| 4 | ActualBinaryMatrixHC46OriginalExactInhabitant | critical re-read | inspected |
| 5 | ActualLeafLabelRankImageAlignment | critical re-read | inspected |
| 6 | ActualAffineRestrictionComposition | new, pinned unconsumed | inspected |
| 7 | ActualAppendFourierCrossLevelOrthogonality | new, consumed | inspected |
| 8 | ActualBinaryGrassmannSamplingBounds | new, consumed | inspected |
| 9 | ActualBinaryMatrixHC46A11WeightedAggregateChecks | new; `#check`/`#print axioms` only | inspected |
| 10–32 | Complexitylib (all 23 modules): Cheeger, EdgeExpansion, Expander, ExpanderExists, ExpanderMerge, ExpanderPad, ExpanderRandom, FamilyFin, MergeGen, Mixing, NumEnc, PermArith, PermCount, PermGraph, Power, RegularGraph, TowerFin, Union, Walk, WalkPath, ZigZag, ZigZagBaseExists, ZigZagTower | new boundary | all inspected |

In the supplied text I found no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` or `opaque`.

## 2. The exported material theorem

**Binders.** `selected_actual_material_moment_bound_original` has the binder list of `selected_actual_material_moment_bound` (I, copies, U, A, C, T, f, base, sourceHeightCutoff, hsel, hA, r, hrd, e, he, hfail, hSpectral, a, ha), in the same order. The only difference is that `hHC` is deleted.

**Conclusion.** The conclusion text matches the original token for token:
- the same `let` block (h, J, c, s, n = 2J, Cc, Tc, fc);
- `∃ k q, k = 2^q ∧ 4m ≤ k < 8m`;
- `matchingStarMass ≤ 2 · selected_actual_analytic_rhs Cc Tc fc r k (2e) a`;
- the exact center-mass identity.

**Proof.** The body is `exact selected_actual_material_moment_bound … hfail original_HC46_exact hSpectral a ha`. The fresh profile is {propext, Classical.choice, Quot.sound}.

**Same consumer throughout.** The PR premise, the moment and the center identity all use the same `Tc = selectedCoordinateLeafTable I copies U A T`, `Cc` and `fc`. `hfail` is stated on that same `Tc`.

**HC46 enters as the general contract, not the leaf wrapper.** It is applied at `hEven := hsplit : c+s = 2h` inside `selected_low_append_HC46_lpNorm_bound`, so the `LeafTable (2*h)` mismatch I noted earlier does not arise. `original_HC46_exact` is universal over every n, d, h, r, i, p and η, so supplying it is legitimate.

**Guards that remain.** `hsel`, `hA : 1 ≤ samplerA`, strict rank `hrd : r < leafT + leafK`, `he : 0 ≤ e`, `hfail`, `hSpectral`, and `ha : 0 < a`.

**Re-checked in AnalyticMoment:**
- Hölder step with exponent `p/m ≥ 1`.
- Dropping the weight via `0 ≤ 1_G ≤ 1` and `(|x|^m)^{k/m} = |x|^k`.
- The root step `(B^k)^{m/k} = B^m`.
- The beta bound, derived from `alpha ≤ 1` and not assumed.
- The low/high split by Fourier reconstruction. This is exact; nothing is supplied by the caller.
- High-level cross terms are removed by the orthogonality proved in file 7.

**Re-checked in AppendMoment:**
- `selected_rankloss_exponent` gives `c + ms + 2h ≤ 2h² < 2J`.
- `rankloss_from_exponent` gives `N0 · 2^{2h-1} ≤ 2^{2J-1}`.

**Re-checked in the Inhabitant.** I re-verified the δ = 0 branch, the i = 0 branch, `hscale` (`10·i·i = 10i²`), the coefficient bound 455 ≤ 500, the density-exponent direction, and the final step `δ^α ≤ η^α`. No hHC is involved. `hEven` is unused when i ≥ 1, which is harmless.

**Re-checked in LeafLabel.** The `decide` congruence is symmetric in orientation. The failed-zoom result is still a one-sided 2e density bound and requires r < d.

## 3. Findings

| ID | Severity | Declaration | Disposition | Remaining question |
|---|---|---|---|---|
| PA1‑01 | Verified | `selected_actual_material_moment_bound_original` | Removes only hHC and states the exact original conclusion (§2). | None in this packet. |
| PA1‑02 | Low (stale) | Module comment in the Application file before the export | It says the export "has not been compiled or independently accepted", but the fresh173 stdout profiles it. The comment carries no weight either way. | Fix before render. |
| PA1‑03 | Low (integration) | The export's type check | `exact` accepted the original's type up to definitional equality, under name resolution in a different file. For example, `CoordAmbient` here vs `…AppendOperator/BinaryMatrixMoment.CoordinateAmbient` there. Both files set the same local `Classical.propDecidable`, so the `if centerMatchBit …` instances agree. | Confirm in the fresh trace that the exported root's type DAG matches the original constant by constant, not just definitionally. |
| PA1‑04 | Medium (fidelity / opportunity) | `Spectral47ExactContract` | **The contract as formalized looks provable without any source premise.** Reviewer sketch, not machine-checked: basis invariance gives `F̂(Z) = F̂(Z U^{-T})`, so coefficients are constant on column-space classes W. `appendAverage` keeps only frequencies `[Y\|0]`, and rank is preserved. By Parseval the energy ratio per class is `∏_{j<i}(2^c−2^j)/(2^{c+s}−2^j) ≤ 2^{-is}`, which is at most the stated `2^{-i(s−1)} + 3·2^{i−n}`. This does not use hEven, ρ, hc, hs or hHeight. So hSpectral is **not** a vacuity risk, and a Spectral47-free material theorem may be within reach. It also suggests the formal contract is weaker than (not the same as) the manuscript's Spectral 4.7. | Machine-check the sketch, and do a manuscript fidelity review of what 4.7 actually states. Spectral47 stays OPEN until then. |
| PA1‑05 | Medium (numeric-NO open) | `selected_actual_analytic_rhs` | The bound is raw. The low part carries `(r+1)^m · 2^{500r²km} ≤ 2^{4000r²m²}` against `(2e)^{≈m−½}`. The high part uses leaf energies the theorem does not bound (they are at most E[1_F] ≤ 1 trivially; not stated). No usefulness theorem exists. | Numeric NO and parameter analysis. |
| PA1‑06 | Low (integration) | `copies` binder | `copies` indexes the tagged tables and U, but nothing ties it to the moment exponent m (the `Instance N m` parameter). | Confirm that being independent of m is intended by the source lane. |
| PA1‑07 | Integration (blocks material completion) | Statements used but proved in other packets | `selected_spectral_parameters` (including how ρ is chosen), `selector_spec`, `sideComplement_finrank`, `matchingStarMass_cast_le_twice_actualAppendRankImageMoment`, `matchingStar/CenterMass_actual_coordinate`, `actualAppendRankImageMoment` (needed for the simpa to `selectedActualMoment`), `ActualFiniteMomentLpBounds.*`, `actualLeafIndicator_mul_right_eq`, `matrix_grassmann_identity`, `alpha_bounds`, `grassmannExperiment_zero_copies`, `ActualFixedFunctionalMatrixLift.failed_zoom_gives_nominal_pseudorandom`. | Need complete-body review in their packets. |
| PA1‑08 | Low | `ActualAffineRestrictionComposition` | Pinned `transitively_consumed:false`, so it is compiled but has no axiom evidence. Content checked: the fibre of the composition is the intersection, and order is subadditive (sup of domains, codimension of the meet). `hbase` is an unused parameter of the def. | Give it no credit beyond being compiled. |
| PA1‑09 | Info | `AppendFourierCrossLevelOrthogonality` | Correct, and unconditional for the uniform base and uniform appended columns. `…mul_eq_zero` only needs Z ≠ Z′, so assuming different ranks is stronger than necessary. `uniformMean_sum` carries an unused `[Fintype α]`. | None. |
| PA1‑10 | Info | `ActualBinaryGrassmannSamplingBounds` | Of this file, only `gaussian_pos` is on the material path (via the beta lemma). I hand-checked the rest: the Weierstrass product bound, frame ≥ ½, the 127/128 window, the pair-product inequality via `1/A + 1/C ≥ 2/B` when `AC = B²`, and the constant 630 ≥ 625·128/127. `hInj` is unused in the probability/mean lemmas, and `bottomBadWindow` is dead code. These depend on ActualFiniteIncidenceSampling, which is pinned unconsumed. | Give the reached constant credit; give the rest credit only as compiled. |
| PA1‑11 | Info | A11 Checks | Harness only; its output was not supplied. Its roots are covered by fresh173. | None. |

## 4. Complexitylib boundary review (all 23 modules)

**Assessment: GO-WITH-NOTES as a boundary.** This is a new review. It is not reuse of an earlier review, and pinning the sources is not acceptance.

**What I verified by reading:**
- **RegularGraph and Mixing.** The rotation map is an involution. The step operator preserves sums, is self-adjoint and is a contraction. The mixing lemma is in squared form.
- **EdgeExpansion.** `(1−λ)·deg·|S||Sᶜ|/n` boundary darts; the sign handling is correct.
- **Union.** Superposition gives `(d_G + d_H·λ)/(d_G + d_H)` without square roots.
- **Cheeger, hard direction.**
  - Co-area: `Σ|ψu−ψw| ≥ 2hd·Σψ`.
  - Cauchy–Schwarz then gives `h²d‖φ‖² ≤ Dirichlet(φ)`.
  - The median split loses nothing (I checked all four sign cases).
  - The lazy walk is positive semidefinite, and semidefinite Cauchy–Schwarz gives `1 − h²/4`.
- **PermCount and PermArith.** I checked `3^31 ≤ 2^52` and `2^20·3^310 ≤ 2^540`, and that `9s ≤ 10k` follows from `t = (s−1)/10`.
- **ExpanderRandom.** The union bound and the geometric slack are done in ℕ without division.
- **PermGraph and ExpanderExists.** Edge expansion is 1/600, degree 120, `randLam = 1 − (1/600)²/4`.
- **ExpanderPad.** Padding with loops uses Jensen.
- **ExpanderMerge and MergeGen.** At most one empty slot per vertex, `N ≥ 2n`, and the bound `√(λ² + (1−λ²)/(2m) + 1/m)`.
- **ZigZag.** The RVW bound `λG + λH + λH²`, both two-sided and after polarization.
- **ZigZagTower.** The invariant `(2/5)² + 1/5 + 1/25 = 2/5`.
- **FamilyFin.** `0.633 ≤ 16/25`, and `famLam = √(1 − 27/(25W)) < 1`.
- **Power and NumEnc.** Correct.

**Is `ExpanderFamily` actually inhabited?** Yes, inside the library: by `randExpander` (counting argument) and by `algFamily` (zig-zag tower). The structure itself is data, not an assumption.

**Notes:**

| ID | Severity | Item |
|---|---|---|
| CX‑01 | Medium (claim boundary) | No computational or runtime theorem exists in these 23 modules. `algFamily`'s base comes from `Classical.choose exists_finBase`, which goes back to `randExpander`. `famRotVal`/`rotVal` are noncomputable. `NumEnc.ofFintype` uses an arbitrary `Fintype.equivFin`. Comments about polynomial time or "an algorithm can read" are not theorems. Encoded reduction and runtime stay OPEN. |
| CX‑02 | Info (representation) | `SpectralBound λ` is a squared contraction on mean-zero functions, so it bounds the absolute value of every nontrivial eigenvalue. Each self-loop is one dart that `rot` fixes. Members with n = 0 are vacuous (`id` rotation). The constants are barely below 1: `randLam ≈ 1 − 6.9·10⁻⁷`, and `famLam` uses `W = 2·deg⁴ + 1` with deg = 120^fifthExp. These are adequate only for qualitative gap statements. |
| CX‑03 | Low (stale) | The `Expander.lean` docstring says no Cheeger or zig-zag construction exists, but the same package proves both. |
| CX‑04 | Info | The import path `Mathlib.Basic.Real.Basic` is unusual. It is consistent with the earlier P8-F8 observation; it compiled under the pinned Mathlib. |
| CX‑05 | Integration | I cannot determine which project modules consume the four modules marked as direct boundaries (Expander, ExpanderPad, FamilyFin, RegularGraph). Candidates are PortCycleReplacement, FixedPortCycleFamily and ActualGraphEdges (consumed) and ExpanderCutInstantiation (unconsumed). I also cannot tell whether they take `E : ExpanderFamily` as a hypothesis or instantiate it with `randExpander`/`algFamily`, or whether the material root reaches them at all. Any `ExpanderFamily` premise must be discharged by those inhabitants, not by citation. |

## 5. Questions carried to integration

1. Complete-body review of the PA1‑07 statements and of the T2′ material imports in other packets (SelectedSpectralParameters, FiniteMomentLpBounds, RankImageRightBasisInvariance, FixedFunctionalBinaryMatrixMoment, FixedFunctionalAppendOperator, ComplementCoordinateMassBridge, MatrixGrassmannIdentity, and the Cmmsa/Tagged/OrdinaryStar families).
2. Trace identity of the exported root's type, constant by constant (PA1‑03).
3. Whether to machine-check PA1‑04, and the manuscript fidelity of Spectral 4.7.
4. Whether `copies` should be tied to m (PA1‑06).
5. Complexitylib consumers and reachability (CX‑05).
6. These remain OPEN: Spectral47, useful numeric NO, source/star/robust8S (`AllAmbientInverse`), encoded reduction, runtime and learning, upstream builds and bridges, inherited warning debt (zero owned warnings ≠ zero total warnings), fresh checkout, manuscript fidelity/render/novelty/citations, and the final providers.

## 6. Safe conditional claim

This rests on the pinned kernel and Init/Mathlib/Batteries trust, the fresh native receipts, and identity-eligible reuse of the 169 prior bodies.

`selected_actual_material_moment_bound_original` holds with standard axioms. Without any hHC premise, for the same I/copies/U/A/C/T/f, and under `hsel`, `hA`, `r < leafT + leafK`, `0 ≤ e`, `hfail`, `hSpectral : Spectral47ExactContract sourceHeightCutoff`, and `0 < a`, it proves:
- there is a dyadic k with `4m ≤ k < 8m` and `matchingStarMass ≤ 2 · selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)`; and
- the exact Grassmann center-mass identity.

**Not claimed:**
- a Spectral47 proof (despite PA1‑04);
- numeric usefulness;
- any computational or runtime property of Complexitylib;
- axiom evidence for unreached declarations (AffineRestrictionComposition, most of SamplingBounds);
- material-scope completion;
- any manuscript verdict.
