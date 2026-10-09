# Spectral47 image-fibre argument: proof-adversarial review

**Scope.** This is an independent review of one argument (hash `39AB07FC…A821`), checked against the `Spectral47ExactContract` definition in both namespaces and the actual `appendAverage` operator. It is not final acceptance, not full327 source coverage, and not a manuscript review. I used no tools, made no writes, ran no Lean/Lake builds and used no subagents.

**Verdict.** The informal argument is mathematically sufficient: it proves a stronger bound than the contract asks for, for every n, c, s, i and every invariant F. No step is wrong. Several steps can be simplified, and the counting/duality/grouping chain can be replaced by a shorter route (section 3). It is not natively ready: the coefficient, rank, count, energy, gain and contract proofs do not exist as declarations yet.

## 1. Complete bodies inspected and skipped

**Inspected in full:**
- `ActualFixedFunctionalAppendOperator.lean`
- `ActualAppendFourierCrossLevelOrthogonality.lean`
- `BinaryMatrixFourier.lean`
- `ActualSelectedComplementSourceSizeAnalyticMoment.lean`
- `ActualSelectedComplementAnalyticMoment.lean` (legacy)
- `SourceSizeContractBridge.lean`
- `BinaryMatrixRightOrbit.lean`
- `BinaryMatrixRightFourierCovariance.lean`
- `BinaryMatrixSameRangeOrbit.lean`
- `MatrixLiftAffineTarget.lean`
- Mathlib: `GeneralLinearGroup/Card.lean`, `Dimension/Finite.lean`, `Dual/Defs.lean`, `Dual/Lemmas.lean`, `Matrix/ToLin.lean`
- The qualified native report JSON

**Imported but not supplied, so skipped:**
- `ActualFixedFunctionalBinaryMatrixMoment`, which holds `coordinateArrayBinaryMatrixEquiv`, `rawTF_eq_unconditional_binaryMatrix_mean` and `actualBinaryMatrixMoment`
- `MatrixLiftNominalDirectComparison` / `MatrixLiftNominalDomain`, which hold `rankImageBoolean`
- `MatrixGrassmannIntersectingAnchor` and the `MatrixGrassmann*` identity modules
- `ActualRankImageRightBasisInvariance`
- `ActualFiniteMomentLpBounds`
- `ActualSelectedComplementSourceSizeAppendMoment` and its legacy counterpart
- `ActualSelectedSpectralParameters`
- `ActualLeafLabelRankImageAlignment`
- The source/star/selector/allocation modules
- The source alignment audit `52295A1A…F511`

**Consequence of the skips.** I relied on these structural facts without seeing their bodies:
- `coordinateArrayBinaryMatrixEquiv` is the column transpose. This is inferred from the `rfl` proofs of `hcol`.
- `appendBinaryMatrixEquiv` is a bijection. Its body is visible, so this one is safe.

## 2. Step-by-step findings

| # | Step | Independent check | Severity | Disposition / action |
|---|---|---|---|---|
| S1 | Transpose direction of Fourier covariance | Σᵢⱼ(Σₖ Yᵢₖ Uₖⱼ)Mᵢⱼ = Σᵢₖ Yᵢₖ(M Uᵀ)ᵢₖ, so pairing(YU, M) = pairing(Y, M Uᵀ). In `fourierCoeff_mul_right_of_basis_invariant`, `hInv` is applied at (Uᵀ, Vᵀ) with UᵀVᵀ = (VU)ᵀ = 1 and VᵀUᵀ = (UV)ᵀ = 1. The reindexing M ↦ M Uᵀ is the bijection `rightBasisEquiv`. The direction is correct. | None | Accepted. Native GREEN covers this helper. |
| S2 | Same-image constancy | `same_range_right_orbit` splits D ≅ W × ker for each surjection; the kernels have equal finrank by rank–nullity, so e satisfies g∘e = f. `toMatrix'_comp` gives N·U = M with paired inverses. "Image" means `range (toLin' Y)`, the column span in F₂ⁿ. Deficient matrices, zero matrices and n = 0 or d = 0 need no special case. | None | Accepted. Native GREEN covers this; body review and consumption trace are still pending. |
| S3 | Coefficient identity FourierCoeff(A_s g, Y) = ĝ([Y 0]) | Direct proof: χ_Y(M) = χ_{[Y 0]}([M B]) by `character_appendBinaryMatrix` and χ₀ = 1. The double average equals the full average because \|Mat(n,c)\|·\|Mat(n,s)\| = \|Mat(n,c+s)\| (`card_prod` plus `Fintype.card_congr appendBinaryMatrixEquiv`). There is no extra normalization factor. `appendAverage_character` is not needed for this route. The argument rightly says cross-level orthogonality does not give the identity. | Translation debt | Sound. Action: add a lemma that a product mean equals the mean over the equivalence. |
| S4 | Rank filter and Parseval | `fourierCoeff_rankProjection` with `fourier_parseval` on Mat(n,c) gives post = Σ_{Y ∈ Mat(n,c)} [rank [Y 0] = i]·F̂([Y 0])². The full-energy identity follows the same way on Mat(n,d). | None | Sound. |
| S5 | Zero-tail embedding preserves image and rank | range(toLin' [Y W]) = range(toLin' Y) ⊔ range(toLin' W), and range(toLin' 0) = ⊥. The existing `appendBinaryMatrix_range_eq_span` is stated only for coordinate arrays. | Translation debt | Sound. Action: prove the matrix-form range-sup lemma, which gives rank [Y 0] = rank Y. |
| S6 | Fixed-image fibre count G(k,i) and its bijections | The forward and reverse maps (corestriction ↔ composition with S ↪ F₂ⁿ) are mutually inverse. Duality is valid here because finite-dimensional spaces over a field are `IsReflexive` (`of_finite_of_free`), and `dualMap_injective_iff` / `dualMap_surjective_iff` hold. Frames ↔ injections is correct. On `card_linearIndependent`: its "k" is our i and its "n" is our k, and it needs i ≤ k. On the i > k branch: `fintype_card_le_finrank` makes the fibre empty. In the i = 0 branch, the only fibre element is the zero map. | Minor (complexity) | Sound but heavier than needed. Duality adds two inverse laws plus naturality of evaluation. A direct alternative avoids it: write Z = B_S·R with R an i×k matrix of full row rank, whose rows form an i-frame in F₂ᵏ. Section 3 removes the count altogether. |
| S7 | Natural-number subtraction in G | `card_linearIndependent` returns a product of `q^n − q^i` in ℕ. Casting to ℝ needs `Nat.cast_sub` with 2ʲ ≤ 2ᵏ for each j < i ≤ k. | Minor trap | Action: discharge this explicitly, or use the section 3 route, which needs no subtraction. |
| S8 | Grouping by image S and representatives | The argument correctly avoids choosing a coefficient for an empty fibre. a_S is defined on Mat(n,d); for Y ∈ Mat(n,c), the identity F̂([Y 0]) = a_S follows from S5 together with S2. | None | Sound. Action: use fibre sums, `Fintype.sum_fiberwise` over the map Z ↦ range. |
| S9 | Ratio bound | 2ˢ(2ᶜ − 2ʲ) ≤ 2^{c+s} − 2ʲ holds iff 2^{j+s} ≥ 2ʲ, which is true. Each factor is ≥ 0 because j < i ≤ c, and the product of i such factors is ≤ 2^{−is}. Positivity of G(d,i) needs i ≤ d, which i ≤ c gives. The i > c branch is handled before any division (post-energy is 0). The i > n and i > d branches are empty. The i = 0 and s = 0 branches give equality. | Minor | Sound. Action: state it in multiplicative form, 2^{is}·G(c,i) ≤ G(d,i), with no division. |
| S10 | Transfer to the contract's real-valued right-hand side | Since 2 ≥ 1 and −i·s ≤ −i·(s−1) for i ≥ 0, `Real.rpow_le_rpow_of_exponent_le` applies; s = 0 is fine. The term 3·2^{i−n} is a positive rpow. Full energy is a mean of squares, so it is ≥ 0. A Nat-pow ↔ rpow bridge is needed: (2^{is})⁻¹ = 2^{−(is:ℝ)} via `rpow_neg` and `rpow_natCast`. | Translation debt | Sound. |
| S11 | Contract shape and guards | The F hypothesis in `Spectral47ExactContract` (∀ M U V, UV = 1 → VU = 1 → F(MU) = F(M)) is exactly what S1 consumes. The other guards (h, ρ, parity, i ≤ c+s, c and s in terms of ρ and h, cutoff ≤ h) are hypotheses, so a proof that never uses them still inhabits the stated contract. The target is unchanged and no guard is removed. `spectral47_contract_iff` is `Iff.rfl`, so one inhabitant serves both namespaces. | None | Sound. |
| S12 | Hidden assumptions | No positive dimension, n ≥ d, full-rank conditioning or source law is used. Finiteness is only `Fintype` of matrices over `ZMod 2`. Choice enters only through existing helpers (the reported axiom profile is Classical.choice, Quot.sound, propext). | None | — |

**Sanity check.** At i = 1 the ratio is (2ᶜ − 1)/(2^{c+s} − 1). That matches counting rank-1 frequencies u·vᵀ whose tail coordinates of v vanish. At i = 0 post-energy equals full energy, as it should for a constant function. The 2197-case audit is consistent with this but certifies nothing.

## 3. Recommended simpler route (it removes S6–S9 entirely)

For Y ∈ Mat(n,c) with rank i, let Ω_Y be the set of W ∈ Mat(n,s) whose columns all lie in the column space of Y. Then |Ω_Y| = (2ⁱ)ˢ, because a subspace of dimension i has 2ⁱ elements (`card_eq_pow_finrank`). For W ∈ Ω_Y:

- [Y W] has the same image as [Y 0], so it has rank i (by S5).
- F̂([Y W]) = F̂([Y 0]) (by S2).

Because (Y, W) ↦ [Y W] is injective (it is `appendBinaryMatrixEquiv`), and every term in the full sum is non-negative:

  full = Σ_{rank Z = i} F̂(Z)² ≥ Σ_{rank Y = i} Σ_{W ∈ Ω_Y} F̂([Y W])² = 2^{is} · Σ_{rank Y = i} F̂([Y 0])² = 2^{is} · post.

This route needs no duality, frame counting, Gaussian product, natural-number subtraction, division, choice of representatives or grouping by subspace. The cases i > c, i > n, i > d, i = 0, s = 0 and zero dimensions are all handled automatically: either a sum is empty or an equality holds. It proves only the inequality, not the exact ratio, but the inequality is all the contract needs.

## 4. Non-claims and complexity audit

- **Scope of the bound.** The bound is a finite identity plus an inequality about the actual unconditional operator. It contains no algorithm or runtime content. No sampler, selection, reduction or learning witness is claimed, and no numeric NO.
- **Not novel.** Mathlib's frame counting (`card_linearIndependent`, `card_GL_field`) is existing work, not new CMMSA counting novelty. If the section 3 route is adopted, it is not needed at all.
- **What native GREEN covers.** It covers only the existing helper declarations listed in the report. The report itself says: `universal_Spectral47_inhabitant_proven: false`, `material_body_review_complete: false`, `consumption_trace_complete: false`.
- **Downstream.** Even with a Spectral47 inhabitant, `selected_actual_material_moment_bound` still takes `HC46ExactContract` as an unproven hypothesis. The cited classical estimate with factor 2^{500 i² p} remains open. Spectral47 also turns out to follow from basis invariance alone, and its 3·2^{i−n} slack is unused. So this inhabitant says nothing about the manuscript's quantitative chain beyond this one step.
- **No overall claims.** There is no overall GO, no manuscript acceptance, no unconditional hardness result and no priority claim.

## 5. Sufficiency vs. readiness

- **Argument sufficiency:** sufficient. It is a sound proof of a stronger statement for the exact contract and operator. The repairs are recommended simplifications (section 3, S7, S9), not fixes for errors.
- **Native/final readiness:** not ready. None of the S3–S5 or S9–S11 statements exist as declarations, and body review and consumption trace are pending.

## Remaining to-do list

1. Native: a lemma that a product mean equals the mean over the append equivalence, and the coefficient identity `fourierCoeff (appendAverage g) Y = fourierCoeff g (appendBinaryMatrix Y 0)`.
2. Native: the matrix-form range lemma for `appendBinaryMatrix Y W` (range sup), and the rank of [Y 0] and of [Y W] when W ∈ Ω_Y.
3. Native: the post-append and full energy identities at rank level i (Parseval plus filter).
4. Native: preferably the injection inequality from section 3, including the card of Ω_Y (= 2^{is}). If the fibre route is kept instead: the corestriction/duality/frame equivalences with both inverse laws, the card with `Nat.cast_sub`, the empty-fibre branches and the multiplicative ratio.
5. Native: the transfer to the contract's rpow right-hand side, then `∀ cutoff, Spectral47ExactContract cutoff` for both namespaces via `spectral47_contract_iff`, with all guards kept in the statement.
6. Bind source, dependency and axiom identities for each new declaration; get independent body review; run a fresh consumption trace through `selected_actual_material_moment_bound_original`.
7. Review the skipped imported bodies listed in section 1, and the source alignment audit `52295A1A…`.
8. Still open:
   - the `HC46ExactContract` inhabitant
   - the source, star, robustness and pre-draw witnesses
   - physical sampling
   - numeric NO
   - encoded selection, runtime, reduction and learning
   - upstream bridges
   - warning and fresh-checkout certification
   - novelty, citations, the PDF and publication gates
