# Proof-adversarial review: Full105 conditional material integration (Full344, Full257, Focused89)

## Verdicts

| Scope | Verdict |
|---|---|
| **Soundness of the 4 fresh files** | **Sound.** I found no defect in soundness, direction, quantifiers, normalization, natural-to-real conversion or edge cases. |
| **Native translation** | **Closed for two things.** The universal inequality-form Spectral47 contract is native in both namespaces. The exact projected-energy equality is native **in frame-count-ratio form**. **Open:** the s-factor eigenvalue product, G/Φ, the restricted adjoint and the full cross-level identity. |
| **Conditional SourceSize/HC46/dyadic integration** | **GO-WITH-NOTES.** For the two original SourceSize exports, **prior HIGH F1 is discharged**. A Low residual remains on the legacy and hHC-parametric exports (F1-r). |
| **Overall readiness** | **Not GO.** R14 (HIGH) is open, and the numeric, source, runtime, upstream, certification and publication gates are also open. |

I used no tools, wrote nothing, and ran no Lean or Lake. Hashes are string comparisons only. Kernel, profile and trace facts come from the receipts.

## 1. Coverage

**Fresh bodies, read in full, every declaration:**

| File | Header SHA | Matches `source_sha256` |
|---|---|---|
| `ActualSelectedComplementSourceSizeSpectralApplication` | 1E985E9A… | yes |
| `…SourceSizeSpectralApplicationChecks` | B0DE8F1D… | yes |
| `ActualFiniteAppendExactImageEnergy` | F3E06B03… | yes |
| `…ExactImageEnergyChecks` | ABF6EA46… | yes |

The object hashes (4512D425…, 91CD1038…, 76B3ED6A…, B7D5648D…) are in a separate category and never collide with the source hashes.

**Parent interfaces re-derived fresh for this integration:**
- SourceSize `OriginalApplication` and the dyadic `…original_at_dyadic_exponent` (binders and conclusions compared token by token).
- Both `Spectral47ExactContract` definitions and the `Iff.rfl` bridge.
- `spectral47_exact_contract_inhabitant`.
- `appendAverage_rankProjection_energy_eq` and `rankProjection_parseval_restricted_eq`.
- `sum_rank_matrices_by_image`, `sum_retained_matrices_by_image` and `RankMatrixType`.
- `retained_fourier_square_sum` and `image_fibre_fourier_square_sum`.
- `card_retainedMatrixImageFibre` and `card_matrixImageFibre`.
- `frameProduct_ratio_le`.

**Inherited, not re-derived in this pass:** the other 88 supplied parent bodies are covered by per-lens identity reuse (8260 contexts unchanged). I make no claim of a fresh reread of all 344 bodies.

**Not supplied, so identity tier only:**
- `GrassmannCounting` (`frameProduct`, `card_frame`) and `BinaryMatrixFourier` (Parseval, coefficient filter).
- The Full104 candidate bytes, so I cannot diff the claimed repair myself.
- Probe output, seal-member listings, and the 9-node trace delta.

**Skipped required fresh bodies: none.**

**Bookkeeping, consistent where checkable:** 251 + 6 = 257 roots; 83 + 6 = 89 focused; 340 + 4 = 344 sources; 687 + 8 = 695 objects; 214 + 2 = 216 modules. The trace grew by 9 nodes, plausibly 6 roots + 2 private lemmas + 1 auxiliary, but this is not enumerated. External boundaries are unchanged at 2762, which is plausible because the new lemmas reuse constants already reached by `GlobalImageEnergy`.

## 2. `ActualSelectedComplementSourceSizeSpectralApplication`

**`selected_actual_material_moment_bound_original_spectral_discharged`**
- **Binders:** exactly the SourceSize `…_original` binder list with `hSpectral` removed: `{N rows m L samplerA}`, `I copies U A C T f base sourceHeightCutoff hsel hA r hrd e he hfail a ha`.
- **Conclusion:** token-identical to the original. The `let` block is unchanged, as are the window `∃ k q, k = 2^q ∧ 4m ≤ k < 8m`, the bound `≤ 2·selected_actual_analytic_rhs(Cc,Tc,fc,r,k,2e,a)`, and the exact Grassmann center identity.
- **Body:** a single `exact` of the original theorem with `hSpectral := (spectral47_contract_iff sourceHeightCutoff).mp (spectral47_exact_contract_inhabitant sourceHeightCutoff)`.
- **Name resolution:** the only analytic namespace opened is SourceSize, so `selected_actual_analytic_rhs` and `selected_actual_source_dimension_bound` resolve to the SourceSize constants. The legacy and dyadic namespaces are not opened.

**`…original_at_dyadic_exponent_spectral_discharged`**
- Same pattern, applied to the dyadic original. The binders `{… k}`, `hkDyadic` and `hkm : 4m ≤ k` are retained, and there is no `k < 8m` ceiling.
- HC46 is still supplied inside the wrapped theorem by the fully qualified `original_HC46_exact`.

**`sourceSize_spectral47_inhabited cutoff`** is the `Iff.mp` transfer, universal in `cutoff`. It inhabits the contract and removes nothing by itself. The removal of `hSpectral` happens only in the two wrappers above.

**Guards preserved from the originals:**
- independent `rows`;
- `I`, copies, U, A, C, T, f;
- `base`, `sourceHeightCutoff`, and `hsel` with the floor `max(analyticSourceHeightFloor …, j+2)`;
- `hA`, `r` with `hrd : r < leafT+leafK`, `e` with `he`;
- `hfail` on the same `selectedCoordinateLeafTable`, which is the same `Tc` used in the PR step and the moment;
- `a` with `ha`;
- the transported tables.

Nothing is replaced by uniform or rank-one noise, by a smaller source or star family, or by a weaker helper.

**Caller exponent P.** The fixed-window export still picks its own `k ∈ [4m, 8m)`. The **dyadic** export is the route for a caller-chosen P: it accepts any dyadic `P ≥ 4m` with no upper bound. A manuscript `P ≥ mT` is therefore accepted when `T ≥ 4` (then `mT ≥ 4m`) and P is dyadic. If some caller has `T < 4`, P must be taken ≥ `max(4m, mT)`. The β exponent is `1 − m/P`, as intended.

**F1 disposition.** F1 is **discharged for these exact conditional formal interfaces**, namely the SourceSize original material export and the dyadic original export. This discharge **does not** supply source witnesses (`U : TaggedGoodU`, `hsel` at a realizable m, `hfail` with a useful e), and it supplies nothing about runtime.

**F1-r (Low, residual):** these exports still take `hSpectral`:
- the legacy m-coupled `ActualSelectedComplementHC46OriginalApplication.selected_actual_material_moment_bound_original`;
- the hHC-parametric `SourceSizeAnalyticMoment.selected_actual_material_moment_bound`;
- the hHC-parametric `…Dyadic….selected_actual_material_moment_bound_at_dyadic_exponent`.

Either mark them superseded or add one-line wrappers.

## 3. `ActualFiniteAppendExactImageEnergy`

**Private helpers:**
- `frameProduct_pos`: for `j < i ≤ d`, `2^j < 2^d`, so every factor is positive. Correct.
- `rank_subtype_sum`: a subtype sum equals the filter sum. Correct.

**`per_image_energy_eq`** (fixed E with `finrank E = i`, `hi : i ≤ c+s`):
- **Empty case:** both sides are empty sums. This branch is in fact unreachable, because `card = G(c+s,i) > 0` under `hi`. It is harmless (Info).
- **Nonempty case:** within the image, the retained sum is `G(c,i)·a²` and the full sum is `G(c+s,i)·a²`. Constancy uses the GL-orbit route **within a single image only**. The quotient is `G(c,i)/G(c+s,i)`, and `field_simp` is justified by the nonzero denominator.
- **i > c:** `frameProduct c i` has the genuine zero factor at `j = c`, so this is not a truncation artifact, and both sides are 0.

**`rank_i_retained_energy_eq`:** exact image partitions of both sums (no representative is chosen for an empty image, and no coefficients are compared across images), with the common quotient pulled out by `Finset.mul_sum`. For `i > n` the index type is empty and both sides are 0.

**`append_rank_projection_energy_eq_frame_ratio`** proves `E_M[(A_s P_iF)²] = (G(c,i)/G(c+s,i))·E_W[(P_iF)²]`:
- It holds for **arbitrary real F** with all-matrix paired-inverse invariance.
- The append law is the actual unconditional one: uniform base, uniform appended block, deficient matrices included.
- Normalization: the left side is the coefficient sum over rank-i, tail-zero frequencies; the right side is Parseval on the full carrier. Each carrier is normalized by its own size, with no stray factor.

**Boundary checks:**

| Case | Result |
|---|---|
| i = 0 | ratio 1/1 |
| s = 0 | ratio 1 |
| c = 0, i ≥ 1 | numerator 0 |
| n = 0 | only rank 0 exists |
| i > c+s | excluded by `hi`; even without it, both sides would be 0 |

**Claimed repair.** The current bodies use `let` (not `letI`) for the `IsEmpty` bindings. That works because local hypotheses of class type are picked up as instances. No `set_option linter…` appears in either fresh file. The declared headers match the intended statements. I cannot check the diff against Full104 because those bytes were not supplied (Info).

**Translation status:**
- **Native:** the count-ratio energy law (diagonal case); cross-level vanishing for i ≠ j (already native via Full90 `uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero`); and the inequality, which follows with `frameProduct_ratio_le`.
- **Untranslated, argument-level only:**
  - `G(c,i)/G(d,i) = Π_{j<s}(2^{d−i}−2^j)/(2^d−2^j)`, including the `d−i < s` zero branch, for which the natural-number subtraction must be handled explicitly;
  - the eigen relation `Φ P_iF = λ_i P_iF`;
  - the G and Φ marginal and completion laws;
  - the restricted adjoint and the full `⟨T P_iF, T P_jF⟩ = λ_j⟨P_iF, P_jF⟩` identity.

Manuscript text must not cite λ_i in product form as formalized.

## 4. Findings

| ID | Sev. | Declaration | Disposition and action |
|---|---|---|---|
| F1 | ~~HIGH~~ → **closed (scoped)** | both `…spectral_discharged` | Spectral premise removed; every other guard and the conclusion retained; standard profiles. |
| F1-r | Low | legacy m-coupled and hHC-parametric exports | Still spectral-conditional. Supersede, or add one-line wrappers. |
| X1 | Verified | the 3 ExactImageEnergy theorems | Exact ratio-form energy law. |
| X2 | Info | `per_image_energy_eq` empty branch | Unreachable under `hi`; harmless. |
| X3 | Medium (translation, carried) | λ_i product, G/Φ, adjoint, full cross-level | Native proofs required, or keep explicitly as argument-level in the manuscript. |
| S1 | Low/Medium (fidelity, carried) | `sourceHeightCutoff` in `hsel` | Formally inert for spectral purposes now; it acts only as a selector floor. Needs a Lemma 4.7 crosswalk. |
| S2 | Info | dyadic export | P must be dyadic and ≥ 4m; P ≥ mT suffices when T ≥ 4. |
| S3 | Low | headers "Uncompiled successor candidate" and "Native verification remains required"; the earlier stale banners | Stale; fix in the next revision. |
| S4 | Info | both Checks harnesses | Contain only `#check`, `#print axioms` and one redundant `example`. Info output, not evidence. |
| S5 | Low (labels, carried) | `universal_Spectral47_inhabitant_proven: false` next to `native_verified: true` | Rename or clarify the flag. |
| R14 | **HIGH (carried)** | encoded reduction and runtime | Bars overall GO. |

## 5. Safe conditional claim

This rests on pinned kernel and library trust, the 257 standard profiles, the qualified trace (8269 nodes, 0 unresolved), and identity reuse.

- For every `rows`, I, copies, U, A, C, T, f, base and cutoff satisfying `hsel`, `1 ≤ samplerA`, `r < c+s`, `0 ≤ e`, `hfail(e)` and `a > 0`, the SourceSize material bound and the center identity hold **with no HC46 premise and no Spectral47 premise**. This covers both the fixed window `k ∈ [4m, 8m)` and every caller-chosen dyadic `k ≥ 4m`.
- For every invariant real F and every `i ≤ c+s`, the post-append rank-i energy equals `G(c,i)/G(c+s,i)` times the full rank-i energy.

**Not claimed:**
- source, selection or global-table witnesses;
- joint arity, source, star, robust8S or pre-draw results; sampling; encoded reduction; runtime or learning;
- numeric NO, `hfail`, e or the scalar parameters;
- λ_i, G/Φ, the adjoint, or manuscript equality in complex-general form;
- exact upstream transports;
- bootstrap or source-object replay;
- inherited-warning certification;
- providers, citations, BibTeX, TeX, PDF or the manuscript;
- novelty or priority (the classical append, Fourier and counting arguments; MZ24 A.13 states only the weaker bound);
- overall GO.

## Remaining to-do

1. F1-r: supersede or wrap the legacy and hHC-parametric spectral-conditional exports.
2. Native λ_i identity: `G(c,i)/G(d,i) = Π_{j<s}(2^{d−i}−2^j)/(2^d−2^j)`, with the zero branch kept explicit. Then the G/Φ completion and marginal laws, the kernel-frame eigenvalue, the invariant-first adjoint, and the full cross-level identity. Each needs independent review.
3. Lemma 4.7 and MZ/MZ24 crosswalk: the inert cutoff, the unused guards and the `+3` slack; wording that the exact eigenvalue is reconstructed rather than quoted from A.13.
4. Numeric NO: certified scalar consumer (`T ≥ 4` or `P ≥ max(4m, mT)`, dyadic), Parseval side conditions, a useful e with `hfail`, choices of `base` and `cutoff`, and an effective L₀.
5. Joint witness for I, copies, U, A and `hsel`; source, star, robust8S and the pre-draw table; the physical sampler.
6. R14: encoded or implicit reduction with a runtime proof; learning.
7. Exact upstream transports: post-audit, then the CMMSA bridges.
8. Custody: Full104 diff bytes, seal-member listings, enumeration of the 9 new nodes, a fresh-checkout replay recomputing all hashes, and a fresh read of `GrassmannCounting` and `BinaryMatrixFourier`.
9. Hygiene: stale headers (S3), flag labels (S5), the legacy hash field, and disposition of inherited warnings.
10. Release: provider, citation, BibTeX, TeX and PDF QA; manuscript fidelity.
