# Full105 complexity review: SourceSize spectral discharge, exact image energy, and full conditional integration

## Verdicts

| Scope | Verdict |
|---|---|
| **Mathematical soundness** of the four fresh files (6 roots, 2 private helpers, 2 Checks harnesses) | **Sound.** I found no defect in soundness, orientation, normalization, boundary handling, quantifiers or vacuity. |
| **Native translation** | **Closed for what the declarations state:** the per-image, rank-i and actual-append exact count-ratio energy equalities, and the transfer of Spectral47 to the SourceSize contract. **Open:** the s-factor eigenvalue product, the G/Φ laws, the restricted adjoint and a packaged cross-level identity. |
| **Conditional integration** (SourceSize, HC46, dyadic, selected leaf) | **GO-WITH-NOTES.** **Prior HIGH F1 is discharged** for the actual SourceSize original export and the caller-chosen dyadic original export. Every other original premise and guard is retained. One Low residual remains: the legacy `m`-coupled export still takes `hSpectral` (C105-04). |
| **Overall readiness** | **Not GO.** R14 (HIGH) is open, as are the numeric, source, runtime, upstream, warning-certification and publication gates. I give no manuscript or publication acceptance. |

**Method.** I used no tools, made no writes, and ran no Lean, Lake or subagents. Hash checks are string comparisons. The headers of all four fresh files match their `source_sha256` values: F3E06B03, ABF6EA46, 1E985E9A and B0DE8F1D. Their objects are kept in a separate category. Compile, profile and trace facts come from receipts.

## 1. Coverage

| Set | Status |
|---|---|
| `ActualFiniteAppendExactImageEnergy` (+Checks) | **Read in full; every declaration re-derived**, including the private `frameProduct_pos` and `rank_subtype_sum` |
| `ActualSelectedComplementSourceSizeSpectralApplication` (+Checks) | **Read in full.** Each binder and the full conclusion were compared token by token against the SourceSize original and dyadic original exports. |
| Parent interfaces these call | Re-checked in this pass:<br>• SourceSize `OriginalApplication`, `ManuscriptDyadicMoment`, `AnalyticMoment` (contract, `selected_actual_material_moment_bound`, RHS, `source_dimension_bound`)<br>• `SourceSizeContractBridge`, `Spectral47ExactInhabitant`, `GlobalImageEnergy`, `PerImageEnergy`, `ImageWeighted`, `FrameProductRatio`, `ImageFibres`, `TailBridge`, `Spectral47` (`appendAverage_rankProjection_energy_eq`)<br>• `HC46OriginalExactInhabitant`, `AppendFourierCrossLevelOrthogonality` |
| Other supplied parent bodies (88 integration sources incl. 23 Complexitylib, 3 Mathlib) | Present and byte-identical. Credit comes from the preserved per-lens reviews; **I did not freshly re-derive all 340 bodies.** |
| Not supplied | `BinaryMatrixFourier`, `GrassmannCounting` (`frameProduct`, `card_frame`), Mathlib `Data/Matrix/Diagonal`, and the remaining ~250 project and ~408 external bodies. These are covered by identity reuse or pinned trust only. |

**Skipped required fresh bodies: none.**

Bookkeeping is consistent:
- roots 251 + 6 = 257; focused 83 + 6 = 89; sources 340 + 4 = 344;
- objects 687 + 8 = 695 (four `.olean` + four `.hash`);
- modules 214 + 2 = 216;
- nodes 8260 → 8269, which fits 6 roots plus the private helpers and auxiliaries (inferred, not enumerated);
- boundaries unchanged at 2762.

## 2. `ActualFiniteAppendExactImageEnergy`

**`per_image_energy_eq`** (fixed `E`, `finrank E = i`, `i ≤ c+s`, real `F`, `basisInv` over all `M` with paired inverses)
- **Empty fibre:** `IsEmpty (MatrixImageFibre …)` makes the retained fibre empty too. Both sides are 0 and no representative is chosen.
- **Nonempty fibre:** a witness `A₀` is drawn from the proved-nonempty fibre. Retained mass = |R|·a² and fibre mass = |M|·a², with constancy coming from the right-GL orbit *inside the same E*. The counts are |R| = G(c,i) and |M| = G(c+s,i). The identity G(c,i)·a² = (G(c,i)/G(c+s,i))·G(c+s,i)·a² uses the positive denominator from `i ≤ c+s`.

**`rank_i_retained_energy_eq`** partitions exactly by image, and the same quotient factors out of every image. Nothing compares coefficients across different images.

**`append_rank_projection_energy_eq_frame_ratio`**

  E_M[(A_s P_iF)²] = (G(c,i)/G(c+s,i)) · E_W[(P_iF)²]

- It applies to the actual unconditional uniform append, with each carrier normalized by its own size (2^{nc} and 2^{n(c+s)}).
- It rewrites `(P_iF)^(Z) = F̂(Z)` on rank-i frequencies, then uses restricted Parseval.
- No Booleanity, conditioning or rank filter on the data is involved.

**Boundary cases**

| Case | Result |
|---|---|
| i = 0 | E = ⊥, G(·,0) = 1, ratio 1: the mean is preserved |
| s = 0 | ratio 1 |
| c = 0 with i > 0 | G(0,i) = 0, so post-append energy is 0 (correct) |
| c < i ≤ c+s | Genuine zero factor j = c; truncated factors only occur after that zero |
| i > n | No rank-i images, so both sides are 0 |
| i > c+s | Excluded by the hypothesis. It would hold anyway, but nothing relies on Lean's 0/0 = 0. |

Natural-to-real conversion is safe: subtraction is untruncated on every j < min(i,c), and the denominator is positive.

**Repairs.** The headers, hypotheses and targets match the stated unchanged forms. The binder `let := hEmpty` is a local instance that is actually used. I cannot compare against the Full104 bytes, which were not supplied. The receipt shows zero owned warnings, and I see no linter disabled in either file.

## 3. `ActualSelectedComplementSourceSizeSpectralApplication`

### 3.1 Guard comparison against the SourceSize original export

| Item | SourceSize original | Spectral-discharged | Same? |
|---|---|---|---|
| `{N rows m L samplerA}`; `I : Instance N rows` (rows independent of `m`) | yes | yes | ✓ |
| `copies`, `U : TaggedGoodU … (blocks samplerA (hBlock L m))`, `A : SideComplement`, `C`, `T`, `f` | yes | yes | ✓ |
| `base`, `sourceHeightCutoff`, `hsel` at `max(analyticSourceHeightFloor …)(j+2)` | yes | yes | ✓ |
| `hA : 1 ≤ samplerA`; `r`, `hrd : r < leafT+leafK` (rank-domain guard) | yes | yes | ✓ |
| `e`, `he`, `hfail` on the same `selectedCoordinateLeafTable` (failed-zoom, exact `q+codim = r`, nonempty zoom) | yes | yes | ✓ |
| `hSpectral` | premise | **removed** | — |
| `a`, `ha` | yes | yes | ✓ |
| Conclusion: same `let` block; `∃ k q, k = 2^q ∧ 4m ≤ k < 8m`; star mass ≤ 2·RHS(Cc,Tc,fc,r,k,2e,a); center = Grassmann fraction | yes | identical | ✓ |

- **Dyadic variant.** It has the same guards plus `k`, `hkDyadic` and `4m ≤ k` with **no upper bound**. A caller's actual P ≥ mT (dyadic, T ≥ 4) is therefore admissible; no fixed 4m ≤ P < 8m shortcut is imposed. Its conclusion matches the dyadic original exactly.
- **Name resolution.** The file opens the SourceSize namespace and not the legacy one, so `selected_actual_analytic_rhs` and `selected_actual_source_dimension_bound` resolve to the SourceSize constants. `exact` was kernel-accepted.
- **How Spectral47 is supplied.** It is passed as `(spectral47_contract_iff cutoff).mp (spectral47_exact_contract_inhabitant cutoff)`, at the caller's own cutoff.
- **How HC46 is supplied.** HC46 continues to be discharged inside the original consumer by `original_HC46_exact`, applied through the universal contract at `hEven := hsplit`.
- **What is unchanged.** The source and star family is not narrowed, the actual append experiment is not replaced by uniform or rank-one noise, and no weaker helper stands in for an obligation.

**`sourceSize_spectral47_inhabited`** is an exact `Iff.mp` transport, universal in the cutoff.

**Disposition of F1: discharged** for these two exact conditional interfaces. This says nothing about whether source witnesses exist, about runtime, or about the remaining premises.

### 3.2 Fidelity consequence

Because Spectral47 now holds for every cutoff, `sourceHeightCutoff` acts only through the selector floor in `hsel`. A caller may take it trivial. This adds no hidden premise, but the cutoff carries no analytic content in the formal lane. The Lemma 4.7 crosswalk must say this explicitly.

## 4. Native results versus argument-level results

| Item | Status |
|---|---|
| Exact energy ratio G(c,i)/G(c+s,i) (per image, rank i, actual append) | **Native** (this packet) |
| Cross-level orthogonality E[A P_iF · A P_jF] = 0 for i ≠ j | **Native** (Full90 `AppendFourierCrossLevelOrthogonality`) |
| Combined ⟨T P_iF, T P_jF⟩ = δ_ij·ratio_i·‖P_iF‖² | **Composable but not packaged.** No single native theorem states it. |
| H-factorization ratio = ∏_{j<s}(2^{d−i}−2^j)/(2^d−2^j), including the zero branch | Argument-level only |
| s-factor eigenvalue Φχ_Y = λ_iχ_Y; G/Φ laws; uniform marginals; independent B/C sampling; restricted invariant-first adjoint | Argument-level only |
| Complex-general manuscript equality; upstream port | Not claimed |

## 5. Findings

| ID | Sev. | Declaration | Disposition and action |
|---|---|---|---|
| C105-01 | Verified | `per_image_energy_eq`, `rank_i_retained_energy_eq`, `append_rank_projection_energy_eq_frame_ratio` | Sound and native |
| C105-02 | **F1 → discharged** | `…original_spectral_discharged`, `…at_dyadic_exponent_spectral_discharged`, `sourceSize_spectral47_inhabited` | Discharged for these exact interfaces |
| C105-03 | Medium (carried FID-1) | Spectral47 contract and cutoff | Cutoff is inert, guards and slack are unused. Do the Lemma 4.7 / MZ24 A.13 crosswalk; attribute the exact eigenvalue as a reconstruction. |
| C105-04 | Low | Legacy `HC46OriginalApplication.selected_actual_material_moment_bound_original` (`Instance N m`) and legacy `AnalyticMoment` material theorem | Both still take legacy `hSpectral`. These are mathematically subsumed (SourceSize with rows := m, by proof irrelevance and delta). Mark them superseded or add a discharged twin. |
| C105-05 | Medium (open) | Exact operator route | Native ratio→λ product, G/Φ, adjoint, and a packaged cross-level identity |
| C105-06 | Low | Stale headers: "Uncompiled successor candidate" (SpectralApplication), "Native verification remains required" (ExactImageEnergy), plus inherited banners | Fix in the next revision |
| C105-07 | Low | `universal_Spectral47_inhabitant_proven: false` beside `native_verified: true`; `exact_manuscript_eigenvalue_and_G_Phi_laws_closed: false` | The label is ambiguous; rename it. The second flag is accurate. |
| C105-08 | Info | Checks harnesses | `#print axioms` and `example` produce info output only, not evidence |
| C105-09 | Low (evidence tier) | `frameProduct`, `card_frame`, `BinaryMatrixFourier`, `transpose_one` | Bodies not supplied; identity reuse or pinned trust. Replay from a fresh checkout. |
| Carried | Medium | Numeric NO (`hfail` / useful `e`, `a`, scalar), joint source/selection/global-table witnesses, joint arity, star/robust8S, pre-draw draws, sampler, encoded reduction, learning | Open |
| **R14** | **HIGH** | Encoded reduction and runtime with doubly exponential J | Open; bars overall GO |

## 6. Safe conditional claim

This rests on:
- pinned kernel and library trust;
- the Full105 receipts: 257 standard profiles, seven stage exits of 0, an 8269-node trace with nothing unresolved;
- the typed identities;
- identity reuse of the 340 bodies.

**Claim 1.** For every real F that is invariant under all paired-inverse right actions, and every n, c, s, i with i ≤ c+s:

  E[(A_s P_iF)²] = (G(c,i)/G(c+s,i))·E[(P_iF)²]

Each image fibre satisfies the same identity.

**Claim 2.** For every `I : Instance N rows`, every copies, U, A, C, T, f, base and cutoff, suppose `hsel`, `1 ≤ samplerA`, `r < c+s`, `0 ≤ e`, `hfail(e)` and `a > 0` all hold. Then, with **no HC46 premise and no Spectral47 premise**, the SourceSize material bound and the exact center identity hold:
- at some dyadic k with 4m ≤ k < 8m; and
- at every caller-chosen dyadic k ≥ 4m.

**Not claimed:**
- the s-factor eigenvalue, G/Φ, the adjoint, or Lemma 4.7 fidelity;
- numeric NO, a useful `e`, or any witnesses;
- source, star, robust8S, sampler, reduction, runtime or learning results;
- upstream transport, fresh-checkout replay, or warning certification;
- novelty or priority (the counting and Fourier argument is classical, and MZ24 A.13 states only the weaker bound);
- overall GO.

## Remaining to-do

1. Native exact operator route: ratio = H-product = ∏_{j<s} λ-factor with the zero branch kept; GL completion and marginals; Φ eigenvalue with independent B/C; invariant-first adjoint; a packaged cross-level identity.
2. Lemma 4.7 / MZ24 A.13 crosswalk: manuscript wording for the inert cutoff and unused guards, and attribution of the exact eigenvalue as a reconstruction.
3. Supersede or discharge the legacy `m`-coupled exports (C105-04). Fix stale headers and flag names (C105-06, C105-07).
4. Numeric NO: a certified scalar consumer (r, T, dyadic P ≥ mT, Parseval side conditions, base/cutoff, effective L₀), then `hfail` at a useful `e`.
5. Joint witness for rows, padded copies, `TaggedGoodU`, A and `hsel`. Source/star/robust8S, pre-draw selection and global table, physical sampler.
6. R14: encoded or implicit reduction with a runtime proof; learning.
7. Upstream post-audit, then the exact CMMSA transports.
8. Fresh-checkout and source-object replay with all hashes and DAG digests recomputed; supply `GrassmannCounting`, `BinaryMatrixFourier` and `Diagonal`; certify the inherited warnings.
9. Final provider, citation, BibTeX, TeX, PDF and manuscript gates.
