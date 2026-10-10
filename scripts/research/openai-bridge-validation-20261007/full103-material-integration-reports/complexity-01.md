# Full103 complexity review: Spectral47 inhabitant, 13 new files, and conditional SourceSize/HC46/dyadic integration

## Verdicts

The 13 new files hold up: I found no mathematical defect. The universal Spectral47 contract now has a kernel-checked proof, but the actual SourceSize and dyadic material theorems still take Spectral47 as an explicit premise, so that HIGH stays open alongside R14. No overall GO.

| Scope | Verdict |
|---|---|
| **Mathematics of the 13 new files** | **Sound.** No soundness, orientation, normalization, boundary or vacuity defect in any declaration. |
| **Native translation of the universal Spectral47 contract** | **Verified for the contract as written.** `spectral47_exact_contract_inhabitant` proves `ActualSelectedComplementAnalyticMoment.Spectral47ExactContract cutoff` for *every* cutoff. It keeps every binder and the +3 term, with the standard axiom profile. The `Iff.rfl` bridge carries it to the SourceSize contract. |
| **Conditional integration, as Full103 claims it** | **GO-WITH-NOTES.** Full103 discharges Spectral47 only in the legacy selected-leaf high-energy lemma, and that is what is checked. |
| **Spectral-free SourceSize/HC46/dyadic material theorems** | **Not delivered. HIGH F1 (carried) stays open.** Every actual SourceSize and dyadic export still takes `hSpectral`. |
| **Manuscript Lemma 4.7, exact eigenvalue, G/Φ, adjoint** | **Not native.** The proved contract is a strictly weaker inequality. |
| **Overall readiness** | **No GO.** R14 (HIGH) and F1 (HIGH) are unresolved; numeric NO, source/runtime and publication gates are open. No manuscript or publication acceptance. |

**Method.** I used no tools, wrote nothing, ran no Lean or Lake, and used no subagents. Hash comparisons are string comparisons of supplied values. Compile results, axiom profiles and trace facts come from the receipts.

## 1. Coverage

| Body set | Count | What I did |
|---|---|---|
| **New files** (13): Spectral47, Spectral47ExactInhabitant, GlobalImageEnergy, PerImageEnergy, TailBridge, ImageWeighted, FrameProductRatio, ImageFibres, ImageOrbit, ImageOrbitFourier, SurjectionCounting, Spectral47OriginalApplication, its Checks file | 13 | **Every declaration read and re-derived** (§2) |
| Parent project bodies supplied: 5 critical, 35 reached, 4 Full95 (SourceSize ×3 and Dyadic), 3 Full97 (SameRangeOrbit, Bridge, MatrixLiftAffineTarget), 2 Full100 (RightOrbit, RightFourierCovariance) | 49 | Read. Fresh re-derivation only where the new files or the integration call sites touch them: contract definitions, `appendAverage_character`, `appendBinaryMatrix_columns`, `uniformMean_sum`/`const_mul`, `selected_leaf_high_energy_le_spectral` in both namespaces, export binders. |
| Complexitylib | 23 | Supplied and byte-identical. Prior full review reused; no new consumer. |
| Mathlib: Rank, ToLin, Finiteness | 3 | Read. Re-checked `rank` as the finrank of the range, `toMatrix'_comp` and `toLin'_apply'`. |

**Skipped required fresh bodies: none.**

Inherited per-lens coverage of the 327 unchanged bodies is **identity reuse, not a fresh reread**. Two bodies the new files depend on are not in this packet:
- `BinaryMatrixFourier` (Parseval, orthogonality, `fourierCoeff_rankProjection`), freshly read in the Full100 addendum.
- `GrassmannCounting` (`frameProduct`, `card_frame`).

Both are identity-reuse only (finding C103-08).

## 2. Audit of the 13 new files

**ActualFiniteAppendSpectral47**
- `pairing_eq_trace_transpose_mul`: Σ Y·M = tr(YᵀM), by reordering sums.
- `pairing_mul_right_transpose`: pairing(YUᵀ, M) = tr(U YᵀM) = tr(YᵀM U) = pairing(Y, MU). The transpose lands on the frequency. This is consistent with Full100's `pairing(YU, M) = pairing(Y, MUᵀ)`.
- `fourierCoeff_mul_right_transpose_eq`: F̂(ZUᵀ) = mean F(M)·χ_Z(MU) = mean F(MU)·χ_Z(MU) using `basisInv`, then reindex by M ↦ MU. Both inverse laws are proved.
- `rank_mul_right_transpose_eq`: det Uᵀ is a unit because U has a right inverse. `V` is unused, which is harmless.
- `rankProjection_mul_right_eq`: invariance of P_i F is **derived** from invariance of F by reindexing frequencies Z ↦ ZUᵀ, which preserves both rank and coefficient. It is not assumed.
- `appendAverage_character_pair` and `appendAverage_rankProjection_energy_eq`:
  - post-append energy = Σ over rank i with zero tail of F̂(Z)², with no normalization factor;
  - the operator is the unconditional uniform append over all matrices.

**ActualFiniteBinarySurjectionCounting.** A map Fin d → Fin i is surjective ⇔ rank = i ⇔ the i rows are independent. Counting independent rows uses `card_frame`, which avoids biduality, as earlier reviewers recommended. When i > d, the j = d factor (2ᵈ − 2ᵈ) makes the product a genuine zero, not a truncation artifact. The general version over arbitrary spaces transports through coordinates, with both inverse laws and surjectivity preserved in each direction.

**ActualFiniteBinaryImageOrbit.** The split V ≃ ker f × E uses a right inverse, and both inverse laws check. Kernel ranks agree by rank–nullity, giving g ∘ U = f. This is a separate proof from the Full97 orbit lemma, with its own native evidence.

**ActualFiniteBinaryImageFibres**
- The fixed-image fibre is equivalent to surjections onto E, with both inverses proved, so its size is frameProduct d i. This holds for E = ⊥, d = 0 and i = 0.
- `appendDomainEquiv`, the injections/projection and `appendDomain_decomposition` check.
- The zero-tail surjection fibre is equivalent to surjections from Coord c onto E:
  - forward map f ∘ inl is surjective because f kills the inr part of the decomposition;
  - inverse g ∘ proj kills inr;
  - both inverse laws are proved.
- Its size is frameProduct c (dim E), including dim E > c.

**ActualFiniteBinaryImageOrbitFourier**
- `exists_right_action_same_image`: two matrices in the **same** fibre satisfy B·U = A, with U, V paired inverses obtained via `toLin'`. The orientation is a right action on domain columns, which preserves the column space.
- `fourierCoeff_rankProjection_eq_same_image`: apply `fourierCoeff_mul_right_transpose_eq` to P_i F with W = Uᵀ and Z = Vᵀ. Then WZ = (VU)ᵀ = 1, and B·Wᵀ = B·U = A. Constancy holds **within one image only**.

**ActualFiniteAppendImageWeighted**
- The retained fibre (surjection kills inr) is equivalent to the zero-tail surjection fibre, with size frameProduct c i.
- `frameProduct_scaled_le`: factor by factor, 2ˢ(2ᶜ − 2ʲ) ≤ 2^(c+s) − 2ʲ. The guard i ≤ c only keeps the natural subtraction exact.

**ActualFiniteFrameProductRatio.** G(c,i)/G(c+s,i) ≤ 2^(−is) for all i: when i > c the numerator is exactly 0. If i > c+s, Lean's 0/0 = 0 also appears, but no downstream use depends on it, because every consumer has i ≤ c+s and a positive denominator.

**ActualFiniteAppendImagePerImageEnergy**
- Retained sum = |R|·a² and full fibre sum = |M|·a², from same-image constancy at a representative A₀.
- With |R| = G(c,i) and |M| = G(c+s,i), the ratio lemma times a² ≥ 0 gives the per-image inequality.

**ActualFiniteAppendImageTailBridge**
- inr(e_j) = e_(natAdd j).
- [Y W] ∘ inr = W, column by column through `appendBinaryMatrix_columns`.
- `retained_iff_appendedFrequencyPart_zero` identifies the counting predicate with the Fourier surviving predicate. This is the key bridge, and it holds in both directions.

**ActualFiniteAppendGlobalImageEnergy**
- `rankMatrixImageEquivSigma` and the retained version are exact reindexings, with the image index taken as the matrix's own range.
- Empty fibres are handled separately, with no representative chosen and no cross-image constancy.
- Per-image inequalities are summed; all share the same factor 2^(−is).
- `append_rank_projection_energy_le` uses F̂(P_i F)(Z) = F̂(F)(Z) on rank-i frequencies.

**ActualFiniteAppendSpectral47ExactInhabitant**
- Restricted Parseval holds.
- 2^(−is) ≤ 2^(−i((s:ℝ) − 1)). The subtraction happens in ℝ, so there is no truncation; s = 0 is fine.
- Every binder is introduced. Only `F`, `basisInv` and `hi` are used; `hEven`, `hRho`, `hc`, `hs` and `hHeight` are retained but unused.
- The +3·2^(i−n) term is nonnegative.

**ActualSelectedComplementSpectral47OriginalApplication.** It applies the **legacy-namespace** `selected_leaf_high_energy_le_spectral` with the inhabitant. All source-height, ρ and split guards stay as hypotheses. **Checks** contains only `#check` and `#print axioms`, which produce info output, not evidence.

### Requested boundary checklist

| Case | Status |
|---|---|
| Zero width (c = 0, s = 0, n = 0, d = 0) | Fine. Singleton carriers, empty products = 1, ratio 1 ≤ 2⁰. |
| i = 0 | E = ⊥, fibre = {0}, frameProduct = 1. |
| i > c | Retained count is a genuine 0 via the j = c factor. |
| i > n | The rank-image index type is empty, so both sides are 0. |
| i > c+s | Excluded by the contract's `hi`. The ratio lemma is still true via 0/0, but nothing relies on that. |
| Deficient and zero matrices | `basisInv` quantifies over all M; the fibres cover every Z. |
| Paired inverses and transpose roles | (UV)ᵀ = VᵀUᵀ handled correctly at each use. |
| Natural to real | Natural subtraction appears only under 2ʲ ≤ 2ᶜ. Exponents are cast before subtracting. |

## 3. Integration

1. **Spectral premise in the actual consumers.** These still require `hSpectral : SourceSize.Spectral47ExactContract sourceHeightCutoff`:
   - `SourceSizeOriginalApplication.selected_actual_material_moment_bound_original`;
   - `ManuscriptDyadicMoment.selected_actual_material_moment_bound(_original)_at_dyadic_exponent`.

   Closing this is now mathematically trivial: `(spectral47_contract_iff _).mp (spectral47_exact_contract_inhabitant _)`. But no such export exists in Full103. The new application also targets the legacy lemma, not the SourceSize copy. **F1 stays HIGH** until a successor export is qualified natively, traced and reviewed. The Full104 four-file candidate is frozen and was not reviewed here.

2. **Unchanged guards.** The SourceSize/HC46 chain carries forward byte-identical:
   - independent `rows` vs leaf arity `m`;
   - one `Tc` in `hfail`, the PR premise and the moment;
   - `hsel`, `hA`, `hrd`, `he`, `ha`, with `hdim`, `hD`, `hsmall` derived;
   - dyadic k ≥ 4m;
   - `original_HC46_exact`;
   - no uniform or rank-one substitute and no smaller source/star family.
3. **No exact equality is claimed.** Fibre counts are exact, so a per-image equality post_E = (G(c,i)/G(c+s,i))·full_E would be a short consequence. Neither it nor the global equality, the H-product identity, G/Φ, the eigenvalue law or the restricted adjoint is native. The separate equality candidate is outside scope.

## 4. Custody and bookkeeping

- **Source hashes.** All 13 `source_sha256` values match the file headers: 2B2A6AFB, 56D96C2C, 4A22102D, 861C5677, 371FD673, 2F8A6758, 0C1610A6, C5670FFE, 10A87647, BA136FC5, 92072C90, 9261DEA4, AA4F9E0F. Object hashes are kept separate; no category is crossed.
- **Counts reconcile:**
  - Roots: 172 + 79 = 251. The 79 are the 20 Full90–Full100 roots plus 59 new (3 + 7 + 3 + 5 + 2 + 2 + 5 + 13 + 1 + 7 + 10 + 1).
  - Focused set: 24 + 59 = 83. Sources: 327 + 13 = 340.
  - Modules: 202 + 12 = 214 (the Checks harness is not in the graph).
  - Objects: 661 + 26 = 687.
  - Nodes 8260 and boundaries 2762 are plausible but not enumerated.

## 5. Findings

| ID | Sev. | Declaration(s) | Evidence | Disposition and action |
|---|---|---|---|---|
| C103-01 | Verified | All 13 new files (§2) | Re-derived | Credit as kernel-checked proofs of the formal statements |
| **C103-02 (F1, carried)** | **HIGH (integration)** | SourceSize original and Dyadic original/material exports | `hSpectral` is still a binder; the new application targets the legacy lemma | Add a successor export composing the inhabitant through `spectral47_contract_iff`; native-qualify, trace, review |
| C103-03 (FID-1, carried) | Medium | `Spectral47ExactContract` | Guards unused; 2^(−is) is strictly stronger than the stated bound; exact eigenvalue, G/Φ and adjoint not native | Keep separate from the manuscript; audit the Lemma 4.7 crosswalk; formalize the exact identities if they are to be cited |
| C103-04 | Low | Native report flags | `universal_Spectral47_inhabitant_proven: false` next to `native_verified: true` | Rename to "accepted/independently reviewed: false"; do not read the flag as either mathematics or acceptance |
| C103-05 | Low | Spectral47OriginalApplication header ("pending … verification"); Checks harness `#print axioms`; inherited stale banners | Superseded by the receipts | Clean up in the next revision |
| C103-06 | Info (warning gate) | `image_fibre_fourier_square_sum` (`have _ := hE`), `per_image_energy_ratio_of_empty` (`have _ := basisInv`) | Linter sinks rather than signature changes | Record under the warning disposition; zero owned warnings ≠ zero total warnings |
| C103-07 | Info | Duplicate orbit and invariance infrastructure (ImageOrbit vs MatrixLiftAffineTarget/SameRange; Spectral47 invariance vs Full100 covariance) | Each has its own native evidence | Consolidate later |
| C103-08 | Low (evidence tier) | `GrassmannCounting.card_frame`/`frameProduct`, `BinaryMatrixFourier` | Not in this packet | Identity reuse only; resupply for any fresh closure claim |
| C103-09 | Info | `retained_fibre_square_sum` local `Fintype.ofFinite` | Elaboration only; compiled | None |
| R14 | **HIGH (carried)** | Encoded reduction/runtime | Unchanged | Bars overall GO |
| Carried Mediums | Medium | Numeric NO, `hfail`/e, joint witnesses, source/star/robust8S, pre-draw table, sampler, upstream transports | Unchanged | Open |

## 6. Safe conditional claim

This rests on pinned kernel and library trust, the Full103 receipts (251 standard profiles, seven stage exits of 0), the GREEN trace and identity reuse.

For every cutoff, the formal Spectral47 contract holds. For every real F invariant under paired-inverse right basis changes, every n, c, s, i with i ≤ c+s, and all retained guards:

  E[(A_s P_i F)²] ≤ 2^(−is)·E[(P_i F)²] ≤ (2^(−i(s−1)) + 3·2^(i−n))·E[(P_i F)²].

The legacy selected-leaf high-energy lemma holds with no Spectral47 premise. The Full95–Full100 SourceSize/dyadic material bounds stand unchanged, **still conditional on `hSpectral`**.

**Not claimed:**
- spectral-free SourceSize or dyadic consumers;
- exact energy equality, eigenvalue, G/Φ or adjoint;
- Lemma 4.7 fidelity;
- numeric NO, a useful e, or witnesses;
- source/star/robust8S, sampler, encoded reduction, runtime or learning;
- upstream bridges, fresh-checkout replay, or zero total warnings;
- novelty or priority (the counting and Fourier arguments are classical; MZ24 A.13 states only a weaker bound);
- any publication acceptance.

## Remaining to-do

1. **F1:** native successor exports composing `spectral47_exact_contract_inhabitant` through `spectral47_contract_iff` into the SourceSize original and dyadic original material theorems, followed by exact trace and fresh review.
2. Optionally native: the exact per-image and global energy equality, the H-product identity, G/Φ, the kernel-frame eigenvalue and the restricted adjoint, if the manuscript is to cite them.
3. Lemma 4.7 and MZ/MZ24 crosswalk (C103-03); manuscript wording that the exact eigenvalue is a reconstruction.
4. Fix the flag semantics (C103-04), stale headers (C103-05), and record the warning sinks (C103-06).
5. Resupply `GrassmannCounting` and `BinaryMatrixFourier` for a fresh read (C103-08).
6. Numeric NO: a useful e with `hfail`, B and Parseval side conditions, `base`/`cutoff`, an effective L₀.
7. Joint source/selector/copies/U/A witness; source/star/robust8S; pre-draw global table; physical sampler.
8. R14: encoded or implicit reduction and runtime; learning.
9. Upstream post-audit, then exact CMMSA bridges.
10. Fresh-checkout replay with every hash and DAG digest recomputed; warning-debt disposition.
11. Release: manuscript fidelity, citation and novelty review, PDF/BibTeX QA, final full-scope providers.
