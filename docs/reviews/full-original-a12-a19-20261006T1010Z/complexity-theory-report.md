# Complexity-theory lens review: original A12 and A19 (frozen capture59)

**Scope.** I looked only at the supplied packet: the target source `ActualBinaryMatrixHC46A12InfluenceBound.lean` (SHA 9AAFDAD1…), the 94 complete sources, the excerpts, and the native/custody receipts. I used no tools and did no compilation. A native-green result tells me the kernel accepted the proofs. My job here is narrower: check that the stated theorems are the intended manuscript results, with honest quantifiers, dimensions, counting and exponents.

## 1. Are the statements the manuscript statements?

**`manuscript_A12_actual`** (source line 283):
- **Binders:** `{n d D : Nat} {eta : Real} (f : BinaryMatrix n d → Complex)`.
- **Premises:** only `ComplexFourierSupportedThrough D f` and `OriginalActualInfluenceThrough D eta f`.
- **Conclusion:** `uniformMean |f|^4 ≤ 2^(103·D^2) · eta · uniformMean |f|^2`.

Everything is universally quantified. There is no Boolean restriction, no `eta ≤ 1`, no positive-D guard, no ambient-width guard and no Q premise. This is manuscript (A12) exactly: ‖f‖₄⁴ ≤ 2^{103d²} η ‖f‖₂².

`OriginalActualInfluenceThrough` (A18OriginalGlobalInduction) quantifies over every A, B and every base T with dim A + codim B ≤ D. Each such T bounds the normalized carrier mean of |filteredCarrierFunction A B T f|². That is the per-base influence I_{A,B,T}, which matches "all influences through order d".

**`manuscript_A19_actual`** (line 300):
- **Premises:** only support and `UpToActualNormSqGlobal D eps f`. The latter covers every `ActualAffineRestriction` of order ≤ D at every base matrix, including order zero. This matches the manuscript's globalness definition.
- **Conclusion:** the 2^{114D²} bound.
- **How it is proved:** it builds the influence premise internally, with parameter 2^{11D²}·eps, by calling `filteredCarrierFunction_energy_le_A16` for every (A, B, T). The cost hypothesis `_hcost` is simply discarded because A16 holds at every cost. There is no extra influence premise and no `eps ≥ 0` premise; A16 derives that internally.
- **Exponent:** 103 + 11 = 114 is a pure `pow_add`/`ring` identity.

## 2. Q bound, counting and normalization

**All-pair squared influence ≤ η × influence** (`a12_energy_square_le`):
- When cost ≤ D: E ≤ η and E ≥ 0, so E² ≤ ηE.
- When cost > D: E = 0 (`a12_energy_zero_above_support`), so 0 ≤ η·0. This branch needs no sign assumption on η.
- The vanishing step is `a12_filter_zero_above_support`. It uses `selected_frequency_rank_lower_bound` (shown in full in A16Assembly): a selected frequency has rank ≥ dim A + codim B. So when cost > D, every selected coefficient has rank > D and is killed by the support hypothesis.

**Q is used exactly as defined.** `a12_Q_le_influence_mass` unfolds `a7HybridQ`/`typedW6QComponent`, the very constant in the conclusion of `manuscript_A7_actual`; Q is not redefined. `a12Energy` is definitionally the carrier mean inside `typedW6QComponent`.

**The averaging step loses no factor.** `a12_energy_mean_eq_mass` reindexes the matrix base mean to the linear-map base mean through `a7MatrixLinEquiv` (shown in the A7 excerpt), with cardinalities proved equal. Applying (A2) (`actual_affine_derivative_energy_eq_selected_fourier_mass`) then gives normalized means on both sides, with no base-count factor. The finite Fubini step uses `Finset.sum_comm` plus `Fintype.card_subtype`. The result is the exact weight #{selected pairs for Y} · |f̂(Y)|². This is a count over the actual pair index `Submodule (V d) × Submodule (W n)`, not over the DR6 three-frequency family.

**Selected pairs ↔ ordered flags in range Y** (`a12SelectedFlagEquiv`). Both inverse laws are proved:
- **Left inverse:** `map(comap A) = A ⊓ range = A` uses A ≤ range Y. `comap(map B) = B` uses ker Y ≤ B, which follows from 0 ∈ A and the preimage condition.
- **Right inverse:** injectivity of the subtype map, and surjectivity of `rangeRestrict`.
- **Membership proofs:** both directions build genuine inclusions.
- **Rank-zero case:** the range is ⊥, so there is exactly one flag. The bound 2^0 = 1 holds.

**Submodule count.** `a12_submodule_card_le_end` maps endomorphisms onto submodules by taking ranges. Surjectivity uses a complement chosen internally (`exists_isCompl`, then `range_projection`); the caller supplies none. That gives #Sub(E) ≤ #End(E) = 2^{(dim E)²}, via `Module.finrank_linearMap` and `ZMod.card`.

**Per-frequency bound.** #flags ≤ #Sub(R)² ≤ 2^{2r²}, where r = rank Y, and 2r² ≤ 3D² whenever r ≤ D. This is sharper than the manuscript's (j+1)²·2^{j²}. Frequencies with rank > D contribute zero.

**The bound is genuinely dimension-free.** Q sums over every subspace pair of the ambient spaces, so the number of terms grows with n and d. The bound does not, because each frequency's multiplicity depends only on its rank, and only ranks ≤ D survive. No ambient-width or dimension factor appears anywhere. This is the essential content, and it holds.

**Closing the Q bound.** Parseval (`complex_fourier_parseval`) turns Σ|f̂|² into the normalized second moment. The nonnegativity η ≥ 0 that the final multiplication needs is derived from the influence premise at (⊥, ⊤, 0), whose cost is 0 ≤ D; this works for D = 0 too (`a12_influence_parameter_nonneg`). The A12 exponent is then 100·D·D + 3D² = 103D², obtained after multiplying by the nonnegative 2^{100DD}.

**Degenerate cases:**
- **D = 0, η = 0:** everything goes through and the bound forces f = 0, consistently.
- **n = 0 or d = 0:** the matrix types are singletons with positive cardinality.

## 3. The A16 path (`filteredCarrierFunction_energy_le_A16`)

- **Canonical flags.** `exists_canonical_source_flags` produces a line flag ⊥→A of length dim A and a hyperplane flag ⊤→B of length codim B, each carrying genuine certificates (finrank of each step quotient equals 1). Total length k = dim A + codim B.
- **k = 0 branch.** It derives A = ⊥ and B = ⊤ from k = 0. The original-to-typed bridge (`actual_global_to_bottomTop_typed`) transports order, fibre and normalized energy exactly. The zero-step translation (`zero_step_carrier_energy_mean`) moves from base T to base 0 with no factor. The final eps ≤ 2^{11D²}·eps uses eps ≥ 0, derived from globalness (`actual_source_parameter_nonneg`).
- **k > 0, ranks below the carrier cost.** Ranks i < k are annihilated by the hybrid filter.
- **k > 0, retained ranks k ≤ i ≤ D.**
  - Residual rank r = i − k. The tower loss is 2^{4rk + 2k² + 4k}, which equals the manuscript's 2^{4kd − 2k² + 4k} with d = r + k, and is ≤ 2^{10D²} (`rankedA15Loss_le_degree`; the D = 0 case is handled).
  - The globalness is the original source's typed globalness at order i ≤ D, at every base.
  - The identification of the retained level with the direct hybrid filter followed by affine restriction (`canonical_source_rank_projection_collapse`) is a proved identity, not a premise.
- **Orthogonality.** `retained_rank_representation` writes each retained level as a typed rank projection at residual rank i − k of its own preimage φᵢ. `typedComplexRankProjection_cross_orthogonal` holds for arbitrary pairs (φ, ψ), so orthogonality across distinct residual ranks with different preimages is legitimate. This is orthogonality between levels, not between colliding individual frequencies, exactly as the manuscript requires.
- **Reconstruction and summation.** Reconstruction over `range (D+1)` comes from support. The bound (D+1) ≤ 2^{D²} holds for all D, including D = 0. The exponent D² + 10D² = 11D².

## 4. Notes and trust limits (none blocking)

1. **`a7_transpose_finrank`** (in A7Transfer; its full source is not in the packet). Its use in `a12_selected_card_le` is pinned by the `have hR : finrank R = Y.rank` type, which is in the target source. It is a standard fact, kernel-checked, and part of the accepted A7 graph.
2. **The (A2) identity in `ActualBinaryMatrixHC46A12FourthMoment`** uses helpers that are not shown (`filteredCarrierFunction_fourier_expansion`, `complexFourierCoeff_character`/`_finset_sum`, probably from A18DerivativeRankProjection). The consumed statement is shown in full. It is already part of the accepted A7 lineage: A7Transfer line ~5340 consumes it.
3. **Omitted A16-closure file `ActualMZ24HyperplaneSupport`** is critical to the proof (hyperplane existence and `relativeCodim`, used in `fullCodomainHyperplaneFlag` and `codomainFlagToSubcarrier`). But the consumer's exported type, including the `finrank (B⧸H) = 1` certificates, is fully visible and kernel-checked under propext/choice/Quot.sound only. It cannot inject a premise. The other omitted outer/star/MZ/covering files are not on the A12/A19 path that I traced. (`ActualFibreModel` and `MatrixLiftNominalDomain` are imported along the way, but the only A16 use of `A18SourceGlobal` is the self-contained `actual_source_parameter_nonneg`.)
4. **Bounds versus claims.** The constants are 2^{103D²} and 2^{114D²}: dimension-free in n and d, but super-exponential in D. They are fourth-moment-only results. This packet does not establish the manuscript's later "all dyadic moments" step, Lp/Spectral47, HC46, or any reduction or hardness consequence. The proposed non-claims are consistent with that.
5. **Harness issues.** The NEW59 offline-assertion error and the receipt KeyError were harness and receipt faults that occurred before or outside proof checking. Proof bytes are unchanged (9AAF/47A8) and all 68 axiom profiles are standard. This has no bearing on the mathematics. The inherited warnings remain open S3137 debt and are not discharged.

**Assumptions:** Lean kernel soundness and the pinned Mathlib library (Projection, `exists_isCompl`, `finrank_linearMap`, `card_eq_pow_finrank`) as trust boundaries, plus the prior three-lens A7 acceptance reused under its documented lineage.

GO-WITH-NOTES
