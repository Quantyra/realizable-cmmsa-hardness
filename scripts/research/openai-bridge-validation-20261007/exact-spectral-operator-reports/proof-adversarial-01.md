# Proof-adversarial review: exact append spectral energy and manuscript operator route

**Not final acceptance.** I read the supplied bodies only. I ran no tools, Lean/Lake builds, writes or subagents, and I did not recompute any SHA-256. Every hash and status label below is copied from the packet. Source inspection here is informal and is not kernel evidence.

## Verdicts

| Question | Verdict |
|---|---|
| **Argument sufficiency** (mathematics only) | **Sufficient.** I re-derived every step and found no mathematical error, no hidden premise and no changed target. The route proves the exact projected-energy equality, its identification with the manuscript eigenvalue, the operator law G T F = Φ F, the kernel-frame eigenvalue, the restricted adjoint, cross-level orthogonality, and the unchanged guarded Spectral47 inequality. It proves that inequality in a strictly stronger form, not as an easier surrogate. Every n/c/s/i boundary listed below holds. |
| **Candidate-native readiness** | **Not ready.** The Full101 chain (11 files) is frozen and was never launched. The exact-energy candidate and its checks file sit outside Full101 and are uncompiled. Nothing exists in Lean yet for the operator laws: completion marginals, the translation step, the kernel-frame eigenvalue, the restricted adjoint, or the product-ratio and real zero-factor identity. Instance and `cast`/`HEq` steps carry elaboration risk (finding A1). |
| **Manuscript readiness** | **Not ready.** The supplied packet does not include the manuscript text, so I could not confirm that MZ Lemma 4.7's operator is this unconditional append. The +3·2^(i−n) term makes that worth checking (finding M1). Numeric NO, source, star, robustness, pre-draw, sampling, reduction, runtime and upstream debt, R14 HIGH, and the warning/provider/final QA gates all stay open. |

## 1. Bodies inspected and skipped

**Read in full:**
- **The argument (complete text):** all sections, including the reviewer-assessment table and the exact-equality and operator section.
- **Full100 native report JSON:** the status flags, the 20 added axiom profiles (all `Classical.choice`, `Quot.sound`, `propext`), and the eight source/object identity pairs.
- **Full100 project sources:**
  - `ActualFixedFunctionalAppendOperator`, `ActualAppendFourierCrossLevelOrthogonality`, `BinaryMatrixFourier`
  - `ActualSelectedComplementSourceSizeAnalyticMoment` and `ActualSelectedComplementAnalyticMoment` (legacy)
  - `BinaryMatrixRightOrbit`, `BinaryMatrixRightFourierCovariance`, `BinaryMatrixSameRangeOrbit`
  - `MatrixLiftAffineTarget`, `SourceSizeContractBridge`, `GrassmannCounting`
- **Full101 frozen/unlaunched (all 11):**
  - `…Spectral47ExactInhabitant`, `…GlobalImageEnergy`, `…ImagePerImageEnergy`, `…ImageTailBridge`
  - `…FrameProductRatio`, `…BinaryImageOrbitFourier`, `…AppendImageWeighted`, `…BinaryImageFibres`
  - `…BinaryImageOrbit`, `…BinarySurjectionCounting`, `…AppendSpectral47`
- **Outside Full101, uncompiled:** `ActualFiniteAppendExactImageEnergy` and `…ExactImageEnergyChecks`.
- **Pinned Mathlib:** `GeneralLinearGroup/Card`, `Dimension/Finite`, `Dual/Defs`, `Dual/Lemmas`, `Matrix/ToLin`, `Matrix/Rank`, `FieldTheory/Finiteness`, `Data/Matrix/Diagonal`, `Matrix/Trace`.

**Not supplied, so not reviewed:**
- The manuscript text: Lemma 4.7, Appendix A and the definition of T.
- The source-alignment audit 52295A1A….
- The full packet 4DF60280… and the three earlier review reports.
- `ActualFixedFunctionalBinaryMatrixMoment`, which holds `coordinateArrayBinaryMatrixEquiv` and `rawTF_eq_unconditional_binaryMatrix_mean`.
- `ActualRankImageRightBasisInvariance`, `ActualFiniteMomentLpBounds`, `ActualSelectedComplement{SourceSize,}AppendMoment`.
- `ActualSelectedComplementSourceSizeOriginalApplication`, `ActualSelectedComplementManuscriptDyadicMoment`.
- `MatrixGrassmann*`, `MatrixLiftNominal*`, `ActualLeafLabelRankImageAlignment`, `ActualSelectedSpectralParameters`.
- Mathlib `Matrix/Basis`, `Dual/Basis`, `FiniteDimensional/Lemmas`, and the rest of the remaining 340-scale closure.

## 2. Step-by-step audit

Notation: G(k,i) = ∏_{j<i}(2^k − 2^j), d = c + s, λ_i = G(d−i,s)/G(d,s).

| # | Step | Math | Severity | Evidence | Required action |
|---|---|---|---|---|---|
| 1 | Paired-inverse Fourier covariance: f̂(YU) = f̂(Y) and f̂(ZUᵀ) = f̂(Z) | Correct in both orientations. pairing(YU, M) = pairing(Y, MUᵀ) by entrywise reindexing, and pairing(YUᵀ, M) = pairing(Y, MU) by the trace argument. Each reindex uses the full carrier bijection M ↦ MUᵀ with explicit inverse Vᵀ. Holds with no rank condition on M or Y. | — | Full100 native (`BinaryMatrixRightFourierCovariance`); Full101 restates it in `…AppendSpectral47` (uncompiled) | **Consumption gap (Medium):** Full101 does not use the native Full100 helper. It re-proves constancy through its own `exists_domain_equiv_of_surjective` and `fourierCoeff_mul_right_transpose_eq`, so native evidence does not transfer to this step. Either consume the native declaration or certify the Full101 copy natively. |
| 2 | Same image ⇒ same right-GL orbit (B·U = A) | Correct. Equal-image surjections differ by a domain automorphism: split each as ker × E and match kernels by dimension. The matrix orientation `(B*U).mulVecLin = B.mulVecLin ∘ U.mulVecLin` is right. Covers deficient maps, E = ⊥ and d = 0. | — | Native (`same_range_right_orbit`); Full101 duplicate in `…BinaryImageOrbit` | Native-certify the Full101 duplicate. |
| 3 | P_i F is invariant | Correct. χ_Z(MU) = χ_{ZUᵀ}(M); coefficients and rank are preserved under Z ↦ ZUᵀ, which is a bijection with inverse ZVᵀ. | — | `rankProjection_mul_right_eq` (uncompiled) | Native-certify. The adjoint step (row 13) depends on it. |
| 4 | Actual append character law: E_B χ_{[Y W]}([M B]) = [W=0]·χ_Y(M) | Correct. The B average is unconditional over all n×s matrices, including zero and dependent ones. | — | Native `appendAverage_character` | None (scope only). |
| 5 | Post-append energy = Σ_{rank Z = i, W = 0} f̂(Z)² | Correct. Pair correlation is [Z = Z′ ∧ W = 0] in all four W/W′ branches. No extra factor: uniform (M, B) reindexes to uniform n×d. | — | `appendAverage_character_pair` and `appendAverage_rankProjection_energy_eq` (uncompiled) | Native-certify. |
| 6 | Full energy = Σ_{rank Z = i} f̂(Z)² | Correct via Parseval and `fourierCoeff_rankProjection`. | — | Native Parseval; `rankProjection_parseval_restricted_eq` (uncompiled) | Native-certify. |
| 7 | Fixed-image count \|{A ∈ n×k : im A = E}\| = G(k,i) | Correct. A ↔ surjection F₂^k → E (corestriction and inclusion, both inverse laws shown) ↔ full-row-rank i×k matrix ↔ independent row i-frame, counted with `card_linearIndependent`. The i > k case is empty via `fintype_card_le_finrank`, matching the j = k zero factor. The i = 0 case is the single zero map with empty product 1, including k = 0. The Lean uses rows rather than the prose's bidual route; this is the sound simplification and makes biduality unnecessary. | — | `…BinarySurjectionCounting` and `…BinaryImageFibres` (uncompiled) | Native-certify. Record that the prose's dualMap route is not the formal route. |
| 8 | Retained fibre (W = 0) ≅ surjections F₂^c → E, count G(c,i) | Correct. f ↦ f∘inl, g ↦ g∘projL; both inverse laws use the decomposition x = inl(projL x) + inr(·) together with f∘inr = 0. Retained predicate ⇔ W = 0 via the tail bridge. | — | `appendedZeroSurjectionEquiv`, `retained_iff_appendedFrequencyPart_zero` (uncompiled) | Native-certify; the `<;> funext j <;> rfl` tail is fragile. |
| 9 | Exact grouping by image, with no representative for empty fibres | Correct. Sigma split over finrank-i subspaces; within each fixed E the coefficient is constant and both fibre sums factor by exact counts; the empty branch is handled separately. For i ≤ d every finrank-i E has a nonempty fibre, so the empty branch only matters for robustness. For i > n the index type is empty and both energies are 0. | — | `sum_rank_matrices_by_image`, `sum_retained_matrices_by_image`, `per_image_energy_eq` | Native-certify; see A1 (cast/HEq). |
| 10 | **Exact energy:** ‖T P_i F‖² = (G(c,i)/G(d,i))·‖P_i F‖² when i ≤ d | Correct. Denominator positive. For c < i ≤ d the numerator count is 0 (zero factor at j = c), so post-append energy is 0. | — | `append_rank_projection_energy_eq_frame_ratio` (outside Full101, uncompiled) | Native-certify inside a frozen lineage. |
| 11 | G(c,i)/G(d,i) = λ_i = ∏_{j<s}(2^{d−i} − 2^j)/(2^d − 2^j) | Correct. Writing G(k,i) = 2^{C(i,2)}·H(k)/H(k−i) gives H(c)H(d−i)/(H(c−i)H(d)) on both sides, using d − s = c and d − i − s = c − i. For c < i ≤ d, both numerators have a zero factor (j = c, and j = d − i < s) while G(d,i) and G(d,s) stay positive. The manuscript product equals G(d−i,s)/G(d,s) factor by factor. **Real conversion:** for j > d − i the real factors are negative, not zero; the product is still 0 only because the j = d − i factor is present whenever s > d − i. d − i is untruncated because i ≤ d. | **Medium (native gap)** | Prose only | Write a native Nat→ℝ product cast with an explicit case split. Do not use `Nat.cast_sub` without `2^j ≤ 2^k`. The proof must use the j = d − i zero factor, not truncation. |
| 12 | G T F = Φ F | Correct. U = [R S] uniform in GL(d). Each full-rank R has ∏_{j=c}^{d−1}(2^d − 2^j) completions, so R is uniform; cardinalities check: G(d,c)·∏_{j=c}^{d−1} = \|GL(d)\|. Inversion is a bijection of GL. With U⁻¹ = [A; C], the identities AR = I, AS = 0, CR = 0, CS = I and RA + SC = I give [MR B]U⁻¹ = M + (B − MS)C. Invariance is applied with matrix U⁻¹ and paired inverse U; no rank condition on M or B. Every s-row frame C has ∏_{j=s}^{d−1}(2^d − 2^j) row completions, so C is uniform full-row-rank. B′ = B − MS is a bijection of all n×s matrices for each fixed U, so (B′, U) is the uniform product law and B′ ⫫ C. B stays unrestricted throughout. Holds only for invariant F, as stated. | **High (native gap)** | Prose only | Translate natively: GL/completion counts and the R and C marginals, inversion bijection, translation bijection, product-measure factorization. |
| 13 | Restricted adjoint ⟨T K, H⟩ = ⟨K, G H⟩ for invariant K | Correct. The product-mean bijection gives ⟨K, H(first c columns)⟩. Average over U, substitute W = W′U⁻¹, use K(W′U⁻¹) = K(W′); the first c columns of a uniform U⁻¹ are uniform full-rank R. Only the first argument needs invariance, and no unrestricted adjoint is claimed. | **High (native gap)** | Prose only | Translate natively. |
| 14 | Φ χ_Y = λ_{rank Y}·χ_Y, hence Φ P_i F = λ_i P_i F for every real F | Correct. tr(Yᵀ B C) = ⟨Y Cᵀ, B⟩, so averaging B gives [Y Cᵀ = 0] (n×s), i.e. every row of C lies in ker Y (dimension d − i). Counting frames gives G(d−i,s)/G(d,s), and 0 when s > d − i. The transpose orientation is right. Linearity needs no invariance. | **High (native gap)** | Prose only | Translate natively. |
| 15 | Second route: ⟨T P_i F, T P_j F⟩ = λ_j δ_ij ‖P_i F‖² | Correct. Combines rows 13 → 12 (applied to P_j F, which needs row 3) → 14 → Fourier rank orthogonality. Independent of rows 7–10 and agrees with row 11, a useful consistency cross-check. Spot checks: (c,s,i) = (1,1,1) gives 1/3 by both routes; (2,1,1) gives 3/7; (2,1,2) gives 1/7; (1,1,2) gives 0. | — | Prose; cross-level orthogonality is native | Translate, or document that the manuscript's eigen and adjoint lemmas are reproved separately. |
| 16 | Cross-level orthogonality after T | Correct for every F, with no invariance needed. | — | Native (`uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero`) | None (scope only). |
| 17 | Gain 2^{s·i}·G(c,i) ≤ G(c+s,i), giving ratio ≤ 2^{−is} ≤ 2^{−i(s−1)} | Correct, including the Nat subtraction step (2^j ≤ 2^s·2^j) and the i > c zero branch. The real exponent form `-(i:ℝ)*((s:ℝ)-1)` matches the contract syntactically; s = 0 is fine. | — | `…FrameProductRatio`, `frameProduct_scaled_le` (uncompiled) | Native-certify. |
| 18 | Contract inhabitant (unchanged guards) | Correct. All binders are introduced. The h, ρ, parity, c/s split and `sourceHeightCutoff ρ ≤ h` guards stay in the statement and go unused, which is legitimate strengthening. `hi : i ≤ c+s` is consumed. The legacy↔SourceSize transfer is the native `Iff.rfl`. | — | `spectral47_exact_contract_inhabitant` (uncompiled) | Native-certify, then bind into `…OriginalApplication` (body not supplied). |

### Boundary sweep (all verified)

| Case | What happens |
|---|---|
| n = 0 | Only the zero matrix exists. Levels i > 0 are empty on both sides; i = 0 gives λ_0 = 1. |
| c = 0 | M is n×0. For i > 0, G(0,i) = 0 and λ_i has the j = d − i zero factor, so both are 0. Φ and G remain well defined. |
| s = 0 | T is the identity (B is n×0), C is 0×d, and λ = 1 = G(c,i)/G(c,i). |
| i = 0 | Empty products; the energy is the squared mean. |
| i > c | Retained energy 0; λ_i = 0 by the zero-factor argument. |
| i > n | No rank-i frequencies; both sides 0. |
| i > d | Excluded by the contract. Lean real division would give x/0 = 0, but no manuscript claim is made there. |
| d = 0 | GL(0) = {∅}; trivial. |

## 3. Findings

**Mathematical errors:** none found.

**M1 — Manuscript operator alignment (High, crosswalk).** The unconditional append operator gives ‖T P_i F‖² = λ_i‖P_i F‖² ≤ 2^{−is}‖P_i F‖², with no 3·2^(i−n) term. That the manuscript states the additive term suggests its Lemma 4.7 may concern a rank- or Grassmann-conditioned operator, or carry slack. Inside the Lean chain the unconditional operator is the one that gets consumed (`rawTF_eq_unconditional_binaryMatrix_mean`, `matchingStarMass ≤ 2·actualAppendRankImageMoment`), so this is not an error in the contract. Still, the claim "proves every exact manuscript equality" depends on T being this operator in the manuscript. **Action:** pin the manuscript's definition of T and the statement of Lemma 4.7 / MZ24 Appendix A in the crosswalk.

**C1 — Consumption-trace gap (Medium).** The Full100 native helpers (`fourierCoeff_eq_of_same_range`, `same_range_right_orbit`) are cited as support but are not consumed by the Full101 chain, which re-proves them. The report itself says `consumption_trace_complete: false`.

**A1 — Elaboration uncertainty (harmless mathematically, blocks native status).**
- **Decidability instances.** Several files declare `attribute [local instance] Classical.propDecidable` while `rankProjection` was elaborated with Nat's `DecidableEq`. The `Finset.filter (· .rank = i)` instances may then differ between `appendAverage_rankProjection_energy_eq`, `rank_subtype_sum` and `rankProjection_parseval_restricted_eq`. That would break the syntactic `rw [← hleft, …]` and `rw [hparseval] at hglobal` steps.
- **Other fragile steps:**
  - `cast`/`HEq` reasoning in the two sigma equivalences.
  - `simp [..] <;> funext j <;> rfl`.
  - `simp_rw [hcoeff] at hglobal` under binders.
  - The `field_simp … <;> ring` closure.
- **Stale banner.** `GrassmannCounting.lean` still carries an "UNCOMPILED" header despite Full100 qualified-native status; this is retained historical bytes.

**N1 — Native translation debt (High).** Rows 11–14 exist only in prose. The exact-energy candidate covers rows 5–10 only, and its own docstring says so.

## 4. Complexity

Everything here is finite existence and counting over exponentially large carriers (2^{nd} matrices, \|GL(d)\|). It uses classical choice: representatives A₀, `Module.finBasis`, right inverses, `LinearEquiv.ofFinrankEq`. There is no algorithm, encoded witness, sampler, selection procedure, reduction, learning procedure or runtime bound. Uniform GL and full-rank laws appear only as finite counting measures, not as samplers. A complete spectral argument implies no hardness and no runtime witness. Numeric NO, source/star/robust8S/pre-draw/sampling/reduction/runtime/upstream debt, and R14 HIGH all remain open.

## 5. Non-claims and evidence tiers

| Tier | Contents |
|---|---|
| Native | Full100 GREEN for its 327 captured sources only: character law, cross-level orthogonality, covariance and orbit helpers, contract bridges. `accepted: false`, `material_body_review_complete: false`, `universal_Spectral47_inhabitant_proven: false`. |
| Uncompiled | All 11 Full101 recovered sources, plus the exact-energy candidate and its checks file outside Full101. |
| Prose | The G/Φ, completion, translation, kernel-frame, product-identity and adjoint steps. |
| Review | This report is informal source inspection, not acceptance. The bounded 2197-case audit is consistency evidence only. |

**Attribution:** the spectral and operator argument is MZ Lemma 4.7 / MZ24 Appendix A. The frame, GL and duality counts are existing Mathlib results (`card_linearIndependent`, `card_GL_field`, `dualMap_*_iff`, `fintype_card_le_finrank`).

**Not claimed:** novelty or priority, an unconditional source or runtime result, fresh-checkout replay, full-340 body review, manuscript acceptance, or publication GO. Warning, provider and final QA gates stay open.

## Remaining to-do list

1. Launch native certification of frozen Full101 (all 11 files). Bind exact source, dependency and axiom identities. Fix or confirm the decidability-instance and cast/HEq steps (A1).
2. Freeze the exact-energy candidate into a lineage and certify it natively (row 10).
3. Either consume the Full100 native covariance and orbit helpers in Full101, or certify the duplicates natively, then complete the consumption trace (C1).
4. Prove natively the Nat→ℝ product identity G(c,i)/G(d,i) = ∏_{j<s}(2^{d−i} − 2^j)/(2^d − 2^j), keeping the explicit j = d − i zero-factor branch (row 11).
5. Translate natively: the GL completion counts and both marginals (R columns, C rows of U⁻¹), the inversion bijection, the translation bijection with B ⫫ C, and G T F = Φ F for invariant F (row 12).
6. Translate natively: the kernel-frame eigenvalue Φχ_Y = λ_i χ_Y, Φ P_i F = λ_i P_i F, and the restricted adjoint for an invariant first argument (rows 13–15).
7. Bind the inhabitant into `…SourceSizeOriginalApplication` and the dyadic consumer, retaining every guard. Review those bodies, which were not supplied here.
8. Manuscript crosswalk: confirm the definition of T and the statements of Lemma 4.7 / Appendix A (M1). Map each exact equality to its Lean declaration.
9. Review the unsupplied imports: Matrix/Rank closure, the coordinate-equivalence module, the source-alignment audit, the moment, Grassmann and alignment modules, and the remaining full-340 bodies.
10. Keep open: numeric NO, source/star/robust8S/pre-draw witnesses, physical sampling, encoded selection/runtime/reduction/learning, upstream transports, R14 HIGH, warnings and fresh-checkout certification, novelty/citations/PDF, the provider gate, final QA, and publication GO.
