# Independent complexity review: E002 / S3137 append spectral image-fibre argument (39AB07FC…A821)

**Verdict.** The mathematical argument is **sufficient**. I re-derived every step myself and found no false step, no hidden assumption and no change of target. It proves a sharper bound than the contract asks for: post-append rank-i energy is at most 2^(−is) times the full rank-i energy, for every n, c, s, i. That sharper bound implies the original Spectral47 right-hand side.

**Native and final readiness is NOT READY.** Spectral47 still has no contract inhabitant. Most of the coefficient, count, energy, gain and contract transports exist only on paper. These two verdicts are reported separately below.

I used no tools, wrote nothing, and ran no Lean, Lake or subagents.

---

## 1. What I read and what I skipped

**Complete bodies inspected:**
- The argument text 39AB07FC…
- The qualified native report 4D580EA6…
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

The source SHA labels in the file headers match the report's `source_sha256` fields for the five added files supplied here. I could not recompute any hash.

**Skipped (not supplied):**
- The source alignment audit 52295A1A…
- The bounded 2197-case ratio audit
- `Mathlib/LinearAlgebra/Matrix/Rank.lean`. I assume the standard definition `rank = finrank (range mulVecLin)`, and the argument depends on it.
- `ActualFiniteMomentLpBounds`
- `ActualRankImageRightBasisInvariance`
- `ActualFixedFunctionalBinaryMatrixMoment`
- `ActualSelectedComplementSourceSizeAppendMoment`
- `ActualSelectedSpectralParameters`
- The `MatrixGrassmann*` modules
- `ActualLeafLabelRankImageAlignment`
- All other files in the 327-source closure

This is not full327 coverage and not a manuscript review.

---

## 2. Step-by-step check

| # | Step | My own derivation | Severity | Disposition | Action |
|---|---|---|---|---|---|
| 1 | Fourier covariance, transpose direction | ⟨YU, M⟩ = Σᵢ,ₖ Yᵢₖ Σⱼ MᵢⱼUₖⱼ = ⟨Y, MUᵀ⟩. Transposing UV = VU = 1 gives VᵀUᵀ = UᵀVᵀ = 1, so the same invariance hypothesis applies to Uᵀ. Reindexing by M ↦ MUᵀ is a bijection. This matches `pairing_mul_right` and `fourierCoeff_mul_right_of_basis_invariant` line for line. | None | Sound; helper is native GREEN | Body review and consumption trace only |
| 2 | Same-image coefficients are equal | Same range ⇒ N·U = M with paired inverses (`same_range_right_orbit` via `surjective_target_orbit` on range-restrictions, so deficient maps are covered). "Image" means the column space of the frequency, which right multiplication preserves. Consistent with step 1. Cases d = 0 and n = 0 are covered (finite-dimensional, no rank hypothesis). | None | Sound; native GREEN | Same as row 1 |
| 3 | Append coefficient identity: coefficient of A_s g at Y equals ĝ([Y 0]) | χ_[Y 0]([M B]) = χ_Y(M)·χ_0(B) = χ_Y(M) (follows from `character_appendBinaryMatrix`). So E_M E_B g([M B])·χ_[Y 0]([M B]) = E_W g(W)·χ_[Y 0](W), using `appendBinaryMatrixEquiv` and \|Mat(n,c)\|·\|Mat(n,s)\| = \|Mat(n,c+s)\|. No extra normalization factor appears. | Major (native gap) | Sound informally; not native | Prove the product-mean = full-mean lemma (`Equiv.sum_comp`, `Fintype.sum_prod_type`, card of product). Either the definitional route or expansion with `appendAverage_character`. The cross-level orthogonality theorem alone is not enough, as the argument itself says. |
| 4 | Rank-level Parseval for both energies | `fourier_parseval` plus `fourierCoeff_rankProjection` give post = Σ_Y [rank [Y 0] = i]·f̂([Y 0])² and full = Σ_Z [rank Z = i]·f̂(Z)². | Major (native gap) | Sound | Compose the existing native lemmas with row 3 |
| 5 | The zero tail preserves image and rank | The columns of [Y 0] are the columns of Y plus zero columns (none when s = 0). Spans are equal, so ranges and ranks are equal. | Major (native gap) | Sound | `Matrix.range_toLin'` plus span-of-union-with-zero; handle s = 0 without a special assumption. `appendBinaryMatrix_apply_castAdd`/`natAdd` are already native. |
| 6 | Fixed-image count: G(k,i) = ∏_{j<i}(2^k − 2^j) | Corestriction bijects matrices with image exactly S onto surjections F2^k → S. Inverse is composition with `S.subtype` and `toMatrix'`; both inverse laws hold because `subtype` is injective and `toLin'`/`toMatrix'` are inverse. Dual route: surjective ⇔ dual map injective (`dualMap_injective_iff`); the reverse direction conjugates by `evalEquiv`; inverse laws come from `eval_naturality` / `dualMap_dualMap_eq_iff`. Frame step: `Basis.constr` and `LinearIndependent.map'`. Count: `card_linearIndependent` with q = 2 and finrank k. Choosing a basis changes the bijection, not the count. | Major (native gap) | Sound, including both inverse laws | See §3 for a simpler route without duality |
| 7 | Impossible and zero branches | i > k: an independent i-frame in a k-dimensional space contradicts `fintype_card_le_finrank`, so the fibre is empty. Note that the ℕ product is then 0 automatically (the j = k factor is 2^k − 2^k = 0), so the formula holds for all i, k. But `card_linearIndependent` needs i ≤ k, so this branch needs its own emptiness proof. i = 0: only the zero map, count 1 (also when k = 0). i > n: no fibres, both sides 0. | Minor | Sound | Prove the i > k branch separately, then show it matches the formula's 0 |
| 8 | Grouping by image and representatives | Full energy = G(d,i)·Σ_S a_S² and post energy = G(c,i)·Σ_S a_S² when i ≤ c. The argument correctly refuses to assign a_S on empty fibres. | Minor (translation risk) | Sound | §3 gives a representative-free form |
| 9 | Gain inequality | For j < i ≤ c: 2^s(2^c − 2^j) = 2^(c+s) − 2^(j+s) ≤ 2^(c+s) − 2^j, with both sides positive. The product gives 2^(is)·G(c,i) ≤ G(d,i) in ℕ. When i > c, G(c,i) = 0, so the ℕ inequality holds for every i. When i > c, the post energy is 0 because rank Y ≤ c. | Major (native gap) | Sound | Prove it in ℕ, without real division. Positivity of G(d,i) is needed only when i ≤ c. |
| 10 | Transfer to the original contract | 2^(−is) ≤ 2^(−i(s−1)) because −is ≤ −is + i, and this holds even for s = 0 since (s:ℝ) − 1 = −1 is fine. 3·2^(i−n) ≥ 0, and full energy ≥ 0. All guards stay as unused binders, so the inhabitant has exactly the type of `Spectral47ExactContract cutoff`. The legacy and SourceSize contracts are `Iff.rfl` (`spectral47_contract_iff`), so one inhabitant serves both. | Minor | Sound | Handle the rpow/natCast/neg conversions carefully (`Real.rpow_le_rpow_of_exponent_le`, `rpow_natCast`, `rpow_neg`) |
| 11 | Changed target or hidden assumption | The argument targets the actual `appendAverage` over all of Mat(n,s), including dependent and zero matrices; the actual `rankProjection` and `uniformMean`; and arbitrary real F with all-matrix paired-inverse invariance. No conditioned surrogate, no rank-conditioned source, and no unused guard is relied on. | None | Target matches | None |
| 12 | Strength of the result | The exact ratio G(c,i)/G(d,i) shows the 3·2^(i−n) term and the −1 in (s−1) are slack. That does no harm, but it means the contract is weaker than what is provable. | Informational | — | Do not present the strengthening as novelty (non-claims below) |

**Steps that depend on items I did not inspect:** that `Matrix.rank` equals the finrank of the `toLin'` range (`Rank.lean` was not supplied), and that a `Fintype` exists for the index of image subspaces if one groups over subspaces. The `Grass` type already has one (`card_grass`), and the route in §3 avoids the question.

---

## 3. Simpler native routes (same mathematics, fewer obligations)

1. **Double count instead of grouping.** Sum over pairs (Y, Z) with range Y = range Z:
   - G(c,i)·Σ_{rank Z = i} f̂(Z)² = Σ_Z Σ_{Y : im Y = im Z} f̂(Z)²
   - In each term, f̂(Z) = f̂([Y 0]) by rows 2 and 5.
   - After `Finset.sum_comm` this equals G(d,i)·Σ_{rank Y = i} f̂([Y 0])².

   This gives **G(d,i)·post = G(c,i)·full**. There is no a_S, no choice of representatives, no empty-fibre case and no subspace index type. It needs only the count lemma for the fibres of a fixed matrix.
2. **Count via a basis matrix instead of duality.** Let B be an n×i injective matrix with range S. Then Y has range S iff Y = BA for a unique A ∈ Mat(i,k) of rank i. Rank i means the rows of A are an independent i-tuple in F2^k, which `card_linearIndependent` counts. This replaces the duality and bidual inverse laws with two coordinate inverse laws. The dual route stays valid if it is preferred.
3. Keep the gain inequality in ℕ (2^(is)·G(c,i) ≤ G(d,i)) and cast to ℝ once at the end.

---

## 4. Complexity lens

- The argument addresses the actual unconditional append operator and the actual dimensions (n×c base, n×s appended block, d = c+s), for all n, c, s, i. It is not a surrogate.
- It is a **finite identity and inequality between finite sums**. It is not an algorithm, sampler, selection procedure, reduction, learner or runtime bound. Translating it natively would give a contract inhabitant, not constructive or encoded computational content.
- No source, sampler, selection, reduction or learning runtime witness is supplied or claimed, and none is implied. That debt stays open. I do not ask for a conditional surrogate in place of the universal target.
- In the downstream consumers, Spectral47 controls only the high-level term (1/a²)·Σ. `HC46ExactContract` is a **separate, still-uninhabited hypothesis** of the same consumer. Inhabiting Spectral47 does not discharge it.

## 5. Non-claims audit

| Claim in the packet | Assessment |
|---|---|
| Frame and dual counts are existing Mathlib results | Correct. `card_linearIndependent`, `dualMap_*_iff` and `fintype_card_le_finrank` are existing Mathlib results, not new counting. The exact G(c,i)/G(d,i) ratio is classical-level finite linear algebra and carries no novelty or priority claim. |
| Native GREEN | Correct but narrow. It covers the twenty listed declarations, including same-range orbit, Fourier covariance and the `Iff.rfl` bridges, with standard axioms only. The report also has `accepted: false`, `local_compilation: false`, `material_body_review_complete: false`, `consumption_trace_complete: false`, `numeric_NO_proven: false` and `universal_Spectral47_inhabitant_proven: false`. All are consistent with the argument's own stated limits. |
| Other open items | Correctly not claimed: the original source, star, robustness and pre-draw witnesses; physical sampling; numeric NO; encoded runtime; upstream bridges; warning and fresh-checkout certification; novelty, citations and PDF; publication. |
| Overall status | There is no overall GO, no manuscript acceptance, no unconditional hardness result and no priority claim. Nothing in the packet overstates its status. |

## 6. Two separate verdicts

- **Is the argument sufficient?** **Yes.** It is complete and correct for all n, c, s, i, including deficient and zero matrices, zero dimensions, i > c, i > d, i > n, i = 0 and s = 0. It has the correct transpose direction and normalization, and both inverse laws of each bijection hold. The only repairs needed are in translation strategy (§3), not in the mathematics.
- **Is the native work ready?** **No.** The Spectral47 inhabitant, the append coefficient identity, the zero-tail rank/image transport, the fibre count, the energy grouping or double count, and the gain inequality are all unproved natively. The exact trace and the fresh body review are pending.

## Remaining to-do list

1. Prove natively the product-mean = full-mean reindexing and the append coefficient identity for the actual `appendAverage`.
2. Assemble rank-level Parseval for both energies from `fourier_parseval` and `fourierCoeff_rankProjection`.
3. Prove the zero-tail range and rank lemma, including s = 0.
4. Prove the fixed-image fibre count, with both inverse laws, via the basis-matrix or dual route. Include the i > k emptiness branch and the i = 0 / k = 0 cases.
5. Prove the identity G(d,i)·post = G(c,i)·full, preferably by double counting.
6. Prove 2^(is)·G(c,i) ≤ G(d,i) in ℕ, handle the i > c branch, and cast to the rpow form of the contract.
7. Build the `Spectral47ExactContract cutoff` inhabitant with every guard binder kept, and transport it through `spectral47_contract_iff`.
8. Bind exact source, dependency and axiom identities. Run the qualified native gates and an independent body review of every new declaration.
9. Complete the exact consumption trace and the fresh integration body review, including the skipped files listed in §1.
10. Supply and review the 52295A1A… alignment audit and confirm the `Matrix.rank` definition it relies on.
11. Still open and not touched by this argument: `HC46ExactContract` inhabitant; source, star, robustness and pre-draw witnesses; physical sampling; numeric NO; encoded selection, runtime, reduction and learning; upstream transports; warning and fresh-checkout certification; full327 coverage; novelty, citations and PDF; publication.
