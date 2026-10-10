# Full103 proof-adversarial review: spectral-family bodies and conditional integration

This review covers Full340, Full251 and Focused83.

## Verdicts

| Scope | Verdict |
|---|---|
| **Mathematical soundness of the 13 new or repaired spectral-family files** | **Sound.** I found no defect in soundness, orientation, quantifiers, normalization, natural-to-real conversion or edge cases. Each of the 59 new declarations was checked. |
| **Native translation of the inequality-form Spectral47 contract** | **Closed.** `spectral47_exact_contract_inhabitant` inhabits the unchanged contract for every cutoff, with standard axioms. |
| **Native translation of the exact manuscript operator laws** | **Open.** This covers the exact eigenvalue, G/Φ, the restricted adjoint and the cross-level equality. |
| **Conditional SourceSize/HC46/Dyadic integration** | **GO-WITH-NOTES, conditional.** The material exports are byte-identical and still require `hSpectral`. Discharging it is now a one-line composition, but that composition is not in the native scope. |
| **Overall GO** | **Not issued.** R14 (HIGH) is open. The prior HIGH finding F1 (Spectral premise remains in the material consumers) is still open as a readiness item. The numeric, source and runtime gates are open. |
| **Manuscript, publication, novelty, priority** | **No verdict.** |

**Method.** I used no tools, wrote nothing, and ran no Lean, Lake or subagents. Every hash comparison below is a string comparison of values in the packet. I recomputed none of them.

## 1. Coverage: fresh review versus inherited reuse

**Fresh, line-by-line review: all 13 new or repaired files, every declaration, nothing skipped.**
- The 11 recovered modules: SurjectionCounting, ImageFibres, ImageOrbit, ImageOrbitFourier, AppendSpectral47, AppendImageWeighted, FrameProductRatio, ImageTailBridge, PerImageEnergy, GlobalImageEnergy and ExactInhabitant.
- The legacy application: `ActualSelectedComplementSpectral47OriginalApplication`.
- Its checks harness.
- Each header SHA matches the `source_sha256` recorded in `added_source_object_identities`. For example, ExactInhabitant is 2F8A6758 and GlobalImageEnergy is 2B2A6AFB; all 13 match. Source and object hash categories were kept separate.

**Re-derived again at the interfaces that are consumed:**
- **Contract definitions and bridge:** both `Spectral47ExactContract` definitions, and `SourceSizeContractBridge`.
- **Selected-leaf energy lemmas:** legacy and SourceSize `selected_leaf_high_energy_le_spectral` and `appendHighLevel_energy_le_spectral_sum`.
- **Append-operator lemmas:** `appendAverage_character`, `appendAverage_rankProjection_sum`, `uniformMean_sum` and `uniformMean_const_mul` in AppendFourierCrossLevel; `appendBinaryMatrixEquiv` and `appendBinaryMatrix_columns`.
- **Mathlib rank results:** `rank_mul_eq_left_of_isUnit_det`, `LinearIndependent.rank_matrix` and `rank_eq_finrank_span_row` in Rank.lean.
- **Material exports:** the SourceSize, Dyadic and HC46 export signatures.

**Read but credited only by inheritance:** the other supplied parent bodies (75 parents in total, including 23 Complexitylib files and 3 Mathlib files). Their bytes are unchanged, and their semantic credit comes from the per-lens Full90–Full100 reviews. I did not re-derive them line by line in this pass and do not claim fresh coverage of the 340 bodies.

**Not supplied, so identity reuse only:**
- `GrassmannCounting`, which holds `frameProduct` and `card_frame`. Their shapes are consistent with how they are used: `∏ j : Fin i, (2^n − 2^j)`.
- `BinaryMatrixFourier`, which was read in full in the Full100 addendum.
- The Mathlib Trace and GeneralLinearGroup.Card modules.
- Roughly 250 other project bodies.

**Bookkeeping checks:**
- Requested axioms: 59 new declarations, and 192 + 59 = 251.
- Focused roots: 24 + 59 = 83.
- Sources: 327 + 13 = 340.
- Graph nodes rose by 176 and external boundaries by 22. Both are plausible, but neither was enumerated.

## 2. Declaration audit of the new files

### ActualFiniteBinarySurjectionCounting

**`matrix_surjective_iff_rows_independent`** (i×d matrix):
- Surjective ⇔ rank = i, from finrank of the range against the codomain finrank i.
- rank = i ⇔ rows independent, using `rank_matrix` and `rank_eq_finrank_span_row` over the field ZMod 2.
- Both directions hold.

**`surjectiveMatrixFrameEquiv` and `card_surjective_coordinate_maps`:**
- The map is d → i, represented by an i×d matrix; that orientation is correct.
- **i ≤ d:** gives `card_frame`.
- **d < i:** frames are empty (`fintype_card_le_finrank`), and `frameProduct d i` has the zero factor 2^d − 2^d at j = d.
- **i = 0:** the empty frame matches the empty product, 1, including d = 0.

**`linearMapCoordinateEquiv` and `card_surjective_linear_maps`:** both inverse laws and both surjectivity directions hold. This uses an independent-row route, so no bidual is needed.

### ActualFiniteBinaryImageFibres

**`matrixImageFibreEquivSurjections`:** a matrix with image exactly E corresponds to a surjection onto E, and back. The left inverse uses injectivity of `toLin'`; the right inverse is by extensionality. `hE` is used only to prove the rank in the inverse direction.

**`card_matrixImageFibre`:** equals `frameProduct d i`, conditioned on the fixed image E. It does not average over images.

**Append-domain decomposition:**
- `appendDomainEquiv` uses `finSumFinEquiv` with the base block first, matching `appendBinaryMatrix`.
- The left and right projections and injections, and `appendDomain_decomposition`, are correct.

**`appendedZeroSurjectionEquiv`** identifies surjections onto E that kill the tail with surjections from `Coord c` onto E:
- Forward surjectivity uses the decomposition together with the tail being killed.
- The inverse kills the tail because `proj ∘ inr = 0`.
- Both inverse laws hold.

**Count:** `frameProduct c (finrank E)`.

### ActualFiniteBinaryImageOrbit

**`exists_domain_equiv_of_surjective`:** `surjectionSplit` gives V ≃ ker f × E through a right inverse, and both inverse laws were checked. The kernel finranks are equal by rank–nullity, giving g ∘ U = f. This duplicates the native Full97 `surjective_target_orbit` (Info only).

### ActualFiniteBinaryImageOrbitFourier

**`exists_right_action_same_image`:**
- `hE` is derived from A; it is not assumed.
- The orientation is B·U = A, because B·mulVecLin ∘ Ue = A·mulVecLin.
- `U*V = 1` and `V*U = 1` hold through `toLin'`.

**`fourierCoeff_rankProjection_eq_same_image`:**
- `rankProjection_mul_right_eq` supplies the invariance of P_iF under every paired inverse.
- `fourierCoeff_mul_right_transpose_eq` is applied at W = Uᵀ and Z = Vᵀ. The required WZ = 1 follows from (VU)ᵀ = 1, and ZW = 1 from (UV)ᵀ = 1.
- Then (P_iF)^(B·Wᵀ) = (P_iF)^(B·U) = (P_iF)^(A).
- Constancy holds only within one image. Nothing compares coefficients across different images.

### ActualFiniteAppendSpectral47

**Transpose and trace lemmas:**
- `pairing_eq_trace_transpose_mul` re-derives as Σ_k Σ_l Y_lk·M_lk.
- `pairing_mul_right_transpose` gives pairing(YUᵀ, M) = pairing(Y, MU). This is consistent with Full100's `pairing_mul_right` under U ↦ Uᵀ.

**`fourierCoeff_mul_right_transpose_eq`:** reindexing by M ↦ MU on the full carrier, with the same denominator.

**`rank_mul_right_transpose_eq`:** the unit determinant comes from `hUV`.

**`rankProjection_mul_right_eq`:** the frequency bijection Z ↦ ZUᵀ has inverse Z ↦ ZVᵀ, since (ZUᵀ)Vᵀ = Z(VU)ᵀ = Z. It preserves both rank and coefficient. This is the A.10 step, for arbitrary real F.

**`appendAverage_character_pair`:** the mean of the product equals [Z = Z′ ∧ tail Z = 0]. All four tail cases were checked, including the mixed cases where Z = Z′ forces equal tails.

**`appendAverage_rankProjection_energy_eq`:**
- Post-append energy equals Σ over rank(Z) = i with tail(Z) = 0 of F̂(Z)².
- The rank filter acts on the full frequency Z = [Y|0] itself. So the inequality route needs no separate zero-tail rank transport.
- The append law is the unconditional uniform base together with the uniform appended matrix.

### ActualFiniteAppendImageWeighted and FrameProductRatio

**`retainedMatrixImageFibreEquiv`:** both inverse laws hold. **`card_retainedMatrixImageFibre`:** equals `frameProduct c i`.

**`frameProduct_scaled_le` (i ≤ c):**
- Factorwise, 2^s(2^c − 2^j) ≤ 2^(c+s) − 2^j, because 2^s·2^j ≥ 2^j.
- The natural-number subtraction is guarded by 2^j ≤ 2^c.

**`frameProduct_scaled_le_all`:** for i > c the left side is zero.

**`frameProduct_ratio_le`:**
- For i ≤ c, the denominator is positive because i ≤ c + s.
- For i > c, the numerator is 0, so 0/x = 0 even when x = 0.
- The cast `((s*i : ℕ) : ℝ)` is handled by `push_cast`.
- There is no truncated-subtraction hazard.

### ActualFiniteAppendImageTailBridge

**`appendRightInjection_single`:** the standard basis vector e_j maps to e_(natAdd c j).

**`appendBinaryMatrix_mulVecLin_comp_right`:** [Y|W] ∘ inr = W, column by column through `appendBinaryMatrix_columns`.

**Equivalences:**
- Tail zero ⇔ Z ∘ inr = 0.
- The retained surjection predicate ⇔ `appendedFrequencyPart` = 0.

The surviving predicate of the spectral calculation is therefore exactly the retained fibre of the counting module.

### PerImageEnergy and GlobalImageEnergy

**Per image:**
- `retained_fourier_square_sum` and `image_fibre_fourier_square_sum` factor by the exact counts through a representative A₀ in a nonempty fibre.
- `per_image_fourier_energy_ratio` multiplies through by 2^(−is) without dividing.

**Global:**
- `rankMatrixImageEquivSigma`, `sum_rank_matrices_by_image` and `sum_retained_matrices_by_image` are exact partitions. The Sigma and cast transport was checked.
- `per_image_energy_ratio_of_empty` handles an empty fibre with no representative: an empty matrix fibre makes the retained fibre empty, so the left side is 0.
- `per_image_energy_ratio` picks a representative only by `Classical.choice` on a proved-nonempty fibre.
- `rank_i_retained_energy_le` sums these over all image subspaces of rank i. If i > n the index type is empty and both sides are 0.

**`append_rank_projection_energy_le`:**
- Post-append energy ≤ 2^(−is) · Σ over rank i of F̂².
- The coefficient conversion uses (P_iF)^(Z) = [rank Z = i]·F̂(Z).

### ActualFiniteAppendSpectral47ExactInhabitant

- **`rankProjection_parseval_restricted_eq`:** Parseval on P_iF, together with the coefficient filter.
- **`append_dyadic_factor_le_spectral_factor`:** compares −is with −i(s − 1) as reals, where (s : ℝ) − 1 is real, not truncated. At s = 0 the comparison is 1 ≤ 2^i.
- **`spectral47_exact_contract_inhabitant`:**
  - The intro order (n c s h i rho F basisInv hEven hi hRho hc hs hHeight) matches the legacy contract binder for binder.
  - Only `basisInv` and `hi` are used.
  - The term 3·2^(i−n) ≥ 0 is handled by `positivity`.
  - The guards are kept in the statement and are left unused.

### Legacy application and checks

**`selected_leaf_high_energy_le_spectral_original_application`:** this is exactly the legacy `selected_leaf_high_energy_le_spectral` with `hSpectral` deleted. Its guards `hEven`, `hRho`, `hc`, `hs` and `hHeight` are retained, and its T and f are generic.

**The checks harness:** contains only `#check` and `#print axioms`. It provides info output, not evidence.

### Edge cases checked

| Case | Result |
|---|---|
| n = 0 | Single matrix, rank 0 |
| i = 0 | Image ⊥, empty products are 1, ratio 1 |
| s = 0 | Tail type is a subsingleton, ratio 1 |
| c = 0, i > 0 | Post-append energy 0 |
| i > c | Retained count 0 |
| i > c + s | Inequality excluded by `hi`; the empty branch is handled anyway |
| i > n | Index type empty |
| Deficient and zero matrices | Covered throughout |
| Paired inverses | Both laws used everywhere |
| Transpose orientation | Consistent across the files |

## 3. Integration

**Unchanged bytes.** The SourceSize AppendMoment, AnalyticMoment, OriginalApplication and Dyadic headers (D4B86B56, 03FB0A5D, 22DE415F, AF3E380A) equal the qualified source identities. So the earlier checks carry forward:
- `Instance N rows` keeps the source row count independent of the leaf count m.
- The same I, copies, U, A, C, T and f are used throughout, with one `Tc` serving `hfail`, the PR premise and the moment.
- c + s = 2h ≤ 2J, with `hdim`, `hD` and `hsmall` derived.
- `original_HC46_exact` is applied at `hEven := hsplit`.
- The dyadic exponent is chosen by the caller, with k ≥ 4m.
- `hsel`, `hA`, `hrd`, `he`, `hfail` and `ha` are kept.
- The append experiment is unconditional and is not narrowed.

**What is still missing.** Every SourceSize and Dyadic export still takes `hSpectral : SourceSize.Spectral47ExactContract sourceHeightCutoff`. By the native inhabitant and the `Iff.rfl` bridge, the term `(spectral47_contract_iff cutoff).mp (spectral47_exact_contract_inhabitant cutoff)` inhabits that premise at every cutoff. That composition is mathematically immediate, but **no qualified native constant performs it**. The Full104 candidate is frozen and unlaunched, so I do not credit it.

**Fidelity consequence.** Because the formal contract holds for every cutoff, the cutoff term inside `analyticSourceHeightFloor` constrains nothing in the formal lane. The formal +3·2^(i−n) and (s − 1) slack are also unused. The contract remains weaker than the manuscript's exact Lemma 4.7 energy and eigenvalue statements.

## 4. Findings

| ID | Severity | Declaration | Disposition | Action |
|---|---|---|---|---|
| S103-1 | Verified | `spectral47_exact_contract_inhabitant` and its 58 supporting declarations | Sound and native | None |
| S103-2 | **HIGH, carried F1 (readiness)** | SourceSize and Dyadic `…material_moment_bound_original*` | `hSpectral` is still a premise, though it is trivially dischargeable | Native successor that composes the inhabitant through `spectral47_contract_iff`, then trace and fresh review |
| S103-3 | Medium (fidelity) | `Spectral47ExactContract`, `analyticSourceHeightFloor` | Guards and slack unused; the cutoff is formally inert | Lemma 4.7 crosswalk; exact eigenvalue, G/Φ, adjoint and cross-level equalities native |
| S103-4 | Low (hygiene) | Spectral47OriginalApplication header ("pending GCP verification"); RightOrbit, Dyadic and SourceSize "uncompiled" banners | Stale | Fix in the next revision |
| S103-5 | Low (labels) | Native flags `universal_Spectral47_inhabitant_proven: false` and `…native_verified: true` | Ambiguous: reads as "review-accepted" versus "kernel-checked" | Rename the flag |
| S103-6 | Info | `have _ := hE` and `have _ := basisInv` in the PerImage and Global files | Unused binders kept to preserve the headers | None |
| S103-7 | Info | Duplicate orbit and covariance routes (ImageOrbit vs. Full97; OrbitFourier vs. Full100) | Both native and consistent | Optional consolidation |
| S103-8 | Info (identity tier) | `frameProduct`, `card_frame`, Fourier bodies | Not supplied; identity reuse only | Fresh-checkout replay |

**Prior findings preserved:**
- **Narrowed:** PA1-04, N-6, SR-3, SP-1, CX100-10 and NC100-5, from "inhabitant open" to "inequality contract closed natively; consumer discharge and exact laws open".
- **Unchanged, open:** numeric NO, `hfail` and `e`; joint source, selection and global-table witness; joint source arity; source, star, robust8S, pre-draw selection, the physical sampler, encoded reduction, runtime and learning; exact upstream transports; fresh checkout and object replay; certification of inherited warnings; and the provider, citation, PDF and manuscript gates.
- **R14 stays HIGH.**

## 5. Safe claim

This rests on pinned kernel and library trust, the Full103 receipts (251 standard profiles, seven stage exits of 0, an 8260-node trace with nothing unresolved), and identity reuse.

**Claimed:**
- For every cutoff and all n, c, s, h, i and rho, with any real F invariant under all paired-inverse right actions, the unconditional append operator satisfies the contract's squared-energy bound with factor 2^(−i(s−1)) + 3·2^(i−n). In fact the sharper factor 2^(−is) holds, with the retained mass on each fixed image exactly G(c,i)/G(c+s,i).
- The legacy selected-leaf high-energy lemma holds with no spectral premise.
- The SourceSize and Dyadic material bounds hold as before, conditional on `hSpectral`.

**Not claimed:**
- Spectral-free native material exports.
- The exact eigenvalue, G/Φ, adjoint or cross-level equalities, or Lemma 4.7 fidelity.
- Numeric NO, source, runtime or learning results.
- Fresh-checkout certification or warning certification.
- Novelty, priority, the manuscript or overall GO.

## Remaining to-do

1. Native successor that discharges `hSpectral` in the SourceSize, Dyadic and HC46 exports through the inhabitant and `spectral47_contract_iff`, followed by a trace and fresh review. This closes F1.
2. Native exact operator route: kernel-frame eigenvalue, Φ and G marginals, invariant-first adjoint, cross-level equality, and the H(t) product identity with its zero branch kept. Then the Lemma 4.7 crosswalk, including how the inert cutoff should be read.
3. Numeric NO: certified scalar consumer, a useful `e` with `hfail`, choices of `base` and `cutoff`, and an effective L₀.
4. Joint witness for I, copies, U, A, C, T, f and `hsel`; source, star and robust8S; the pre-draw table; the physical sampler.
5. R14: encoded or implicit reduction with a runtime proof; learning.
6. Upstream post-audit, then the CMMSA bridges.
7. Fresh-checkout replay, recomputing source, object and type-DAG hashes, including the unsupplied GrassmannCounting and Fourier bodies.
8. Hygiene: stale banners, flag naming, the legacy hash field, and disposition of inherited warnings.
9. Release: manuscript fidelity, novelty and citations, PDF, final providers.
