# Non-claims review, Full90 material consumer, packet 1 of 5

## Verdict: GO-WITH-NOTES for this packet only

This is not a verdict on the whole material review, the whole manuscript, or acceptance. The overall material-review state is still INCOMPLETE until the other four packets and the final integration are done.

**How this was reviewed**
- I used no tools, ran no code, wrote no files and started no subagents.
- I did not run Lean or Lake, and I did not recompute any hashes.
- I took the native facts from the qualification text you supplied:
  - 7 stage exits of 0;
  - 173 requested roots;
  - a standard profile for `selected_actual_material_moment_bound_original`;
  - 319 source pins and 566 unchanged objects;
  - the trace with 194 consumed modules and 2738 external boundaries.
- References are by declaration name, not line number.

## Coverage: 32 complete files supplied, 32 inspected, 0 skipped

| Group | Files | Status |
|---|---|---|
| Changed material export | `ActualSelectedComplementHC46OriginalApplication` | Inspected in full |
| Four unchanged critical bodies, re-read | `ActualSelectedComplementAnalyticMoment`, `ActualSelectedComplementAppendMoment`, `ActualBinaryMatrixHC46OriginalExactInhabitant`, `ActualLeafLabelRankImageAlignment` | Inspected in full |
| New or changed project files | `ActualAffineRestrictionComposition`, `ActualAppendFourierCrossLevelOrthogonality`, `ActualBinaryGrassmannSamplingBounds`, `ActualBinaryMatrixHC46A11WeightedAggregateChecks` (a `#check`/`#print axioms` harness) | Inspected in full |
| Complexitylib, all 23 modules | Cheeger, EdgeExpansion, Expander, ExpanderExists, ExpanderMerge, ExpanderPad, ExpanderRandom, FamilyFin, MergeGen, Mixing, NumEnc, PermArith, PermCount, PermGraph, Power, RegularGraph, TowerFin, Union, Walk, WalkPath, ZigZag, ZigZagBaseExists, ZigZagTower | Inspected in full (reading only; no tactic replay) |

**Text scan.** None of the 32 files contains `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` or `opaque`. This is a text-level check only. Fresh axiom evidence exists only for constants the 173 roots reach.

## 1. The exported material theorem

The theorem is `selected_actual_material_moment_bound_original`.

**Exactly `hHC` is removed, and nothing else.**
- The binders are the original theorem's binders minus `hHC`:
  - implicit `{N m L samplerA}`;
  - `I copies U A C T f base sourceHeightCutoff hsel hA r hrd e he hfail hSpectral a ha`.
- The body is one `exact` call to `selected_actual_material_moment_bound`, passing the same arguments in the same order, with `original_HC46_exact` in the `hHC` slot.
- Because the body is a direct `exact` and the module compiled, the exported conclusion is definitionally the original conclusion. I also compared the two texts and they match:
  - the same `let h J c s n Cc Tc fc`;
  - `∃ k q, k = 2^q ∧ 4m ≤ k < 8m`;
  - the same `matchingStarMass` on `A.1` with the transported tables, bounded by `2 · selected_actual_analytic_rhs … Cc Tc fc r k (2·e) a`;
  - the same center-mass identity.

**No substitution or weaker form is used.**
- The proof does not route through `selected_leaf_HC46_original`, whose `LeafTable (2*h)` type would not match `c+s` here.
- It supplies the universal `HC46ExactContract`. Inside, that contract is used at `b = selectedF Tc fc` with `hEven := hsplit`.

**The same objects are used throughout.**
- The failed-zoom PR premise, the HC/spectral moment and `hfail` all use the same coordinate leaf `Tc`.
- The mass bound (`selected_actual_append_moment` from AppendMoment) and the center identity are taken at the same `I copies U A C T f` and the same `analyticSourceHeightFloor base sourceHeightCutoff`.
- The two Grassmann betas, over `CoordinateAmbient (2J)` and over `CoordAmbient J`, agree only definitionally. The source text here does not show that; the successful compile does.

**Premises the export still keeps:** `hSpectral`, `hsel`, `hA`, `hrd`, `he`, `hfail`, `ha`.

**Non-vacuity.** I don't see these premises as obviously contradictory.
- By my hand reasoning, Spectral47 is plausibly true: coefficients are constant on column-space orbits, which gives a fraction of at most `2^{-is}`. That is reasoning, not a proof.
- `hfail` holds trivially for large `e`.
- Whether `hsel` can be satisfied depends on the selector definition, which is not in this packet.

**Axiom profile.** The profile is `[propext, Classical.choice, Quot.sound]`.
- It now covers `selected_actual_material_moment_bound` and AppendMoment, which the pins now mark `transitively_consumed: true`. This corrects the Full89 tier, where AppendMoment was compiled but unreached.
- A clean profile does not mean the `Prop` premises `hSpectral` and `hfail` are discharged. Premises do not appear in axiom output.

## 2. The four critical re-reads

Each matches its pinned prior review, and I found no change in direction or quantifiers.
- **OriginalExactInhabitant.** Re-checked: η ≥ 0 is derived; δ = min(η, 1); the δ = 0 branch; i = 0 is delegated; coefficient 455 ≤ 500; exponent p − 2 + 2/p ≥ p − 2 with δ ≤ 1.
- **AnalyticMoment.**
  - The low/high decomposition is exact Fourier reconstruction.
  - HC is applied per level, only when `i ≤ r`.
  - Hölder uses `p/m ≥ 1`; `hlowroot` gives `k · (m/k) = m`.
  - Beta domination uses `alpha ≤ 1`.
  - The high part uses cross-level orthogonality and then Spectral47.
- **AppendMoment.** Re-checked `c + m·s + 2h ≤ 2h² < 2J` (from `m+2 ≤ h`) and the rank-loss factor ≤ 1/2.
- **LeafLabel.** It is a pure transport `leafMatchBit = matchingLeafSet`. It gives a one-sided PR at 2e.

## 3. Findings

| ID | Severity | Declaration or location | Finding | Disposition |
|---|---|---|---|---|
| N1 | Low (documentation) | OriginalApplication, `/-!` block above the material export | It says "This candidate has not been compiled or independently accepted." The native receipt contradicts the first half. | Stale text with no evidential weight either way. Fix before render. |
| N2 | Medium (claim boundary) | `selected_actual_material_moment_bound_original` | Still conditional on Spectral47, the selector, failed-zoom and positive-parameter premises. Nothing shows the RHS is small: the low term is about `(Σ_{i≤r} 2^{500 i² k} (2e)^{(k−2)/k})^m`, and the high energies are unbounded with a free `a`. | Must be cited as a conditional material bound. Numeric NO stays open. |
| N3 | Medium (Complexitylib overclaim) | `Expander.lean` module docstring | It says neither Mathlib nor this library has a spectral gap, edge expansion, Cheeger or zig-zag result. The same package now proves all of these. | Stale; no weight. |
| N4 | Medium (computational claim) | `FamilyFin.algFamily`, `famRotVal`, `fitLevel_le`, NumEnc `ofFintype` docstrings | "Explicit … rotation tables an algorithm can read" and "the polynomial … is linear" are informal. `algBase := Classical.choose exists_finBase` is seeded from `randExpander` by `Classical.choose`. Every definition is `noncomputable`. There is no runtime theorem: `level ≤ 2n` does not bound the `2^level` recursive calls in `rotVal`. | Claim no explicitness, computability or polynomial-time property. This touches the encoded-reduction and runtime gates, which stay open. |
| N5 | Medium (constants) | `randLam`, `fifthExp`, `FinBase.famDeg`, `famLam` | `randLam = 1 − (1/600)²/4`. The base degree is `120^{fifthExp}`, where `fifthExp` is a `Classical.choose` exponent that is unspecified (the needed m is roughly 2·10⁶ or more). `famLam = √(1 − 27/(25(2·deg⁴+1)))`. So the constant degree and gap are existential and astronomically bad. | Make no numeric constant claim downstream of any Complexitylib family. |
| N6 | Info (representation) | `RegGraph`, `SpectralBound`, `ExpanderFamily` | Rotation-map multigraphs with loops and parallel edges. Members exist at every n, including n = 0 (vacuous). `SpectralBound` is a two-sided operator-norm bound on mean-zero vectors, which is stronger than a second-eigenvalue bound. Lazy padding (`padLoops`) and folding (`mergedN`, `famRot`, with id at n = 0) change the graph. | Consumers must not read "simple graph" or one-sided λ₂. |
| N7 | Info | `ExpanderRandom.exists_good_perms` | Proves existence only. The docstring's "a random tuple works" is not exported as a probability bound. | No sampling or high-probability claim. |
| N8 | Info (verified) | Cheeger, Union, Power, ZigZag, ZigZagTower, MergeGen, ExpanderPad | Rechecked by hand:<br>• Cheeger: h²·d‖f‖² ≤ Dir and a lazy bound of 1 − h²/4 via a semidefinite Cauchy–Schwarz argument.<br>• Union: (d_G + d_H·λ)/(d_G + d_H).<br>• Power: λᵗ.<br>• RVW (zig-zag): λ_G + λ_H + λ_H², with polarisation to an operator bound.<br>• Tower invariant: 4/25 + 1/5 + 1/25 = 2/5.<br>• Merge at m ≥ 3: 0.633 ≤ 0.64.<br>• Padding: 1 − (9/25)α ≤ 1 − 27/(25W). | Holds by reading. Kernel acceptance is covered only for reached constants. |
| N9 | Info | `ActualBinaryGrassmannSamplingBounds` | Pair product ≤ square holds by AM-GM because AC = B². The 127/128 and 630 constants hold (625·128/127 ≈ 629.9). `hInj` is unused in several lemmas, and `bottomBadWindow` is unused. The header excludes advice, Section 8 and CMMSA. | Pinned as consumed, but probably only through `gaussian_pos`. Credit nothing else without trace membership. |
| N10 | Info | `ActualAffineRestrictionComposition` | Correct by reading (codim of an intersection ≤ sum of codims). Pinned `transitively_consumed: false`. | Compiled only; no profile and no credit. |
| N11 | Info | `ActualAppendFourierCrossLevelOrthogonality` | The character factorisation and cross-level zero are exact. `appendZeroFrequency` is dead code, and the local name `uniformMean_sum` could collide with another. | No action needed. |
| N12 | Low | AnalyticMoment docstrings (`selected_actual_event_moment_bound` "sole remaining obligation"; `/-!` text on definitions) and AppendMoment's unused `hle`/`hp` | Retained from earlier reviews. | Hygiene. |
| N13 | Info | A11 Checks harness | Its `#print axioms` output was not supplied. The A11 roots are covered by the fresh 173-root stdout. | No action needed. |
| N14 | Info | `RegularGraph` imports `Mathlib.Basic.Real.Basic`; Complexitylib uses `module`, `public import` and `@[expose]` | Unusual paths and the module system. The pinned compile resolves them. | Note for fresh-checkout replay. |

## 4. Questions for integration

1. **How the project uses Complexitylib.** Which project module consumes the four directly reached modules (Expander, ExpanderPad, FamilyFin, RegularGraph), and does it take `E : ExpanderFamily` as a hypothesis or the concrete `randExpander`/`algFamily`?
   - The interface is inhabited inside the library by `randExpander` and `algFamily`.
   - That does not certify any source or manuscript expander statement, explicitness, or constant.
2. **Definitions not in this packet:**
   - `PseudorandomExact`, `selector`/`selector_spec`, `analyticSourceHeightFloor`, `selected_spectral_parameters`
   - `matchingStarMass`/`matchingCenterMass`, `transported*Table`, `selectedCoordinate*Table`, `coordinateFunctional`, `CoordAmbient`, `TaggedGoodU`, `SideComplement`
   - `matchingStarMass_cast_le_twice_actualAppendRankImageMoment`, `matchingStarMass_actual_coordinate`, `matchingCenterMass_actual_coordinate`
   - `matrix_grassmann_identity`, `alpha_bounds`, `finite_sum_lpNorm_le`, `appendAverage_lpNorm_le`, `actualLeafIndicator_mul_right_eq`, `failed_zoom_gives_nominal_pseudorandom`, `relativeDeviationEvent`
3. **Open premises.** Can `hsel` be satisfied for some L? Is Spectral47 inhabited at the instantiated cutoff? Can `hfail` be met with a useful e?
4. **Trace membership.** Which constants from SamplingBounds and Complexitylib are actually reached? The 2738 boundaries should be enumerated before anything is credited by name.

## 5. Safe conditional claim

Under the qualified native receipts, the pinned trust in the kernel, Init, Mathlib and Batteries, and the unreviewed-but-pinned Complexitylib bodies, the following holds:
- `selected_actual_material_moment_bound_original` proves the identical original material conclusion for the same `I copies U A C T f`, coordinate tables and functional.
- Its bound is `matchingStarMass ≤ 2 · selected_actual_analytic_rhs(…, 2e, a)` with dyadic k in [4m, 8m), together with the exact center-mass Grassmann identity.
- It discharges only the `hHC` premise, using `original_HC46_exact`. It remains conditional on `hSpectral`, `hsel`, `hA`, `hrd`, `0 ≤ e`, `hfail` and `0 < a`.
- Its axiom profile is standard.

**Not claimed:**
- Spectral47; useful numeric NO;
- source/star/robust8S; encoded reduction; runtime or learning;
- expander explicitness, computability or constants;
- a reviewed proof of any manuscript expander interface;
- standard profiles for unreached declarations;
- zero total warnings (the inherited warning debt stays open);
- fresh-checkout replay, manuscript fidelity, render, novelty or citations;
- final providers, or any whole-manuscript verdict or acceptance.
