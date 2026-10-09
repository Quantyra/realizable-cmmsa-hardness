# Independent complexity review: actual append spectral route, Full101 exact-energy candidate and manuscript operator argument

**Scope.** This review is based only on reading the supplied texts. I used no tools, wrote no files, ran no Lean or Lake, and used no subagents. It is not final acceptance. Nothing below turns reading a source into proof acceptance.

**Bottom line.** I found no mathematical error and no changed target. The argument looks sufficient for every exact manuscript equality and for the unchanged guarded inequality. That is a reviewer's judgement, not kernel evidence. The candidate is not native-ready, and the manuscript is not ready.

## 1. Bodies I inspected and what I skipped

**Inspected in full (all 37 supplied bodies):**
- **The complete argument** (SHA 153D…80A3F).
- **The Full100 native report** (SHA 4D58…83A4).
- **Full100-qualified project sources (12):**
  - ActualFixedFunctionalAppendOperator
  - ActualAppendFourierCrossLevelOrthogonality
  - BinaryMatrixFourier
  - ActualSelectedComplementSourceSizeAnalyticMoment
  - BinaryMatrixRightOrbit
  - BinaryMatrixRightFourierCovariance
  - BinaryMatrixSameRangeOrbit
  - MatrixLiftAffineTarget
  - SourceSizeContractBridge
  - ActualSelectedComplementAnalyticMoment
  - GrassmannCounting
- **Full101 frozen sources, never launched (11):**
  - Spectral47ExactInhabitant
  - GlobalImageEnergy
  - PerImageEnergy
  - ImageTailBridge
  - FrameProductRatio
  - BinaryImageOrbitFourier
  - AppendImageWeighted
  - BinaryImageFibres
  - BinaryImageOrbit
  - BinarySurjectionCounting
  - AppendSpectral47
- **Outside Full101, uncompiled (2):** ActualFiniteAppendExactImageEnergy and its Checks file.
- **Pinned Mathlib (9):** GeneralLinearGroup/Card, Dimension/Finite, Dual/Defs, Dual/Lemmas, Matrix/ToLin, Matrix/Rank, FieldTheory/Finiteness, Matrix/Diagonal, Matrix/Trace.

**Imported but not supplied, so not reviewed:**
- **Project modules:** ActualFixedFunctionalBinaryMatrixMoment (it defines `coordinateArrayBinaryMatrixEquiv`), ActualRankImageRightBasisInvariance, ActualFiniteMomentLpBounds, ActualSelectedComplement(SourceSize)AppendMoment, ActualSelectedSpectralParameters, ActualLeafLabelRankImageAlignment, MatrixLiftNominal*, MatrixGrassmann*, GrassmannIncidence and TripleRestrictionRank.
- **Mathlib modules:** Projection, RankNullity, Algebra/Module/Projective, GeneralLinearGroup/Defs, `equiv_linearIndependent`, `card_compl_set` and Matrix/Block.
- **Other:** the standalone source-alignment audit (52295A…F511) and the manuscript text of MZ Lemma 4.7 / MZ24 Appendix A.

**Stale banners kept as historical bytes.** GrassmannCounting still says "UNCOMPILED companion", and BinaryMatrixRightOrbit says "not native qualified". The native report says both declaration sets were native-verified. I took the report as authoritative for their status but did not upgrade anything beyond it.

## 2. Step-by-step check

Severity scale: **none** means a correct mathematical step; **elab** means harmless elaboration uncertainty; **transport** means a missing native or source transport; **math** would mean a mathematical error. I found no math-severity items.

| # | Step | My independent check | Evidence tier | Severity | Required action |
|---|---|---|---|---|---|
| 1 | **Actual unconditional append.** A_s g(M) = mean over all n×s matrices B of g([M B]), with dependent and zero matrices included. | `appendAverage` is a `uniformMean` over every `BinaryMatrix n s`. `appendBinaryMatrixEquiv` keeps base columns first via `finSumFinEquiv`, and both inverse laws are proved. | Full100 native | none | Consumption trace into the Full101 inhabitant. |
| 2 | **Coefficient identity.** FourierCoeff(A_s g, Y) = ĝ([Y 0]). | `character_appendBinaryMatrix` factorises the character. `appendAverage_character` gives [W=0]·χ_Y, using orthogonality of χ_W against χ_0. Normalisation is the product of uniform means, with no extra factor. | Full100 native | none | – |
| 3 | **Rank-level energy.** mean (A_s P_i F)² = Σ over rank(Z)=i with tail zero of f̂(Z)². | `appendAverage_character_pair` and `appendAverage_rankProjection_energy_eq` collapse the double sum on the diagonal, using `uniformMean_sum` and `uniformMean_const_mul`. Staying in Z-space avoids needing rank([Y 0]) = rank(Y). | Full101 frozen, uncompiled | transport | Native compile and profile. |
| 4 | **Same-image coefficient constancy.** | Two derivations, both orientation-checked. Full100 route: `fourierCoeff_mul_right_of_basis_invariant` reindexes by Uᵀ/Vᵀ, then `basis_invariant_eq_of_same_range`. Full101 route: `exists_right_action_same_image` gives B·U = A, then `fourierCoeff_mul_right_transpose_eq` with W = Uᵀ, so B·Wᵀ = B·U = A. `rankProjection_mul_right_eq` makes P_i F invariant, as the projected coefficients need. | Full100 native / Full101 frozen | none / transport | Bind the Full100 declarations rather than duplicating them, or certify both natively. |
| 5 | **Fixed-image fibre count G(k,i).** | Matrix ↔ surjection onto E: `codRestrict` forward, `E.subtype ∘ f` back, with both laws. Surjection ↔ independent rows: rank = i ↔ rows independent, via `rank_eq_finrank_span_row` over a field. Then `card_linearIndependent` gives ∏_{j<i}(2^k − 2^j). For i > k the frame type is empty by `fintype_card_le_finrank`, and the product has a zero factor at j = k. For i = 0 the count is 1, including k = 0. The Lean route uses row frames, not the duality route in the prose, so the pinned dualMap APIs are not consumed. That is acceptable. | Full101 frozen + Mathlib text | transport | Native compile. Note in the crosswalk that the duality prose is replaced by the row route. |
| 6 | **Retained (zero-tail) fibre count G(c,i).** | `appendedZeroSurjectionEquiv`: f ↦ f∘inl, and g ↦ g∘proj. The left-inverse law uses x = inl(proj x) + inr(snd x) and the tail kill. `retained_iff_appendedFrequencyPart_zero` ties this to the operator's survival predicate; the column orientation natAdd c j = inr j checks out. | Full101 frozen | transport (elab risk in the `hproj` `<;> funext j <;> rfl` and `appendBinaryMatrix_mulVecLin_comp_right` simp chains) | Native compile. |
| 7 | **Grouping by image without representatives for empty fibres.** | `rankMatrixImageEquivSigma` and `sum_retained_matrices_by_image` use Sigma/HEq transports. Empty fibres are handled by an `IsEmpty` branch. A representative is chosen by `Classical.choice` only inside nonempty fibres. | Full101 frozen | transport (elab risk in the Sigma.ext/cast proofs) | Native compile. |
| 8 | **Exact ratio: post-append energy = G(c,i)/G(d,i) × full energy when i ≤ d.** | `per_image_energy_eq` and `append_rank_projection_energy_eq_frame_ratio`. The denominator is positive because i ≤ c+s. For i > c the numerator count is 0. For i > n there are no subspaces, so both sides are 0. | Outside Full101, uncompiled | transport | Native compile plus `#print axioms`. The Checks file has not run. |
| 9 | **Bound G(c,i)/G(d,i) ≤ 2^(−is).** | Each factor satisfies 2^s(2^c − 2^j) ≤ 2^(c+s) − 2^j. The i > c branch is handled before any division. | Full101 frozen | transport | – |
| 10 | **H-factorisation.** G(c,i)/G(d,i) = G(d−i,s)/G(d,s). | Pulling 2^j out of each factor gives G(k,t) = 2^(t(t−1)/2)·H(k)/H(k−t) for t ≤ k. Both sides then equal H(c)H(d−i)/(H(c−i)H(d)), using d−s = c and d−i−s = c−i. For c < i ≤ d: the first product has its j = c zero factor, and the second has its j = d−i zero factor because d−i < s. Denominators are positive since i, s ≤ d. | Informal only | transport | Translate natively. |
| 11 | **Natural/real conversion of the zero factor.** | Lean's `frameProduct` uses truncated ℕ subtraction. The index j runs contiguously from 0, so whenever some j > k occurs, the j = k factor is already 0 in both ℕ and ℝ. Truncation therefore never changes the product. | Informal only | transport | State the lemma explicitly; do not rely on cast-pushing. |
| 12 | **GL completion marginals in both directions.** | Forward: every full-column-rank R (d×c, c ≤ d) has exactly ∏_{j=c}^{d−1}(2^d − 2^j) > 0 completions, so R is uniform. Reverse: inversion is a bijection on the finite group GL(d), so U⁻¹ is uniform. Its bottom s rows C have exactly ∏_{j=s}^{d−1}(2^d − 2^j) row completions each, so C is uniform over full-row-rank matrices. The carriers are nonempty because c, s ≤ d. | Informal only | transport | Native cardinality and pushforward lemmas, with both inverse laws. |
| 13 | **G T F = Φ F.** | From U U⁻¹ = I we get R C′ + S C = I, so [MR B]·U⁻¹ = MRC′ + BC = M + (B − MS)C. Invariance applies to the pair (U⁻¹, U) with no rank condition on M or B. B ↦ B − MS is a bijection of the whole n×s carrier for each fixed U, so the new B is uniform conditional on U and hence independent of C. B is never replaced by a full-rank draw. | Informal only | transport | Translate natively, with exact source-shaped definitions of G and Φ. |
| 14 | **Kernel-frame eigenvalue.** Φχ_Y = λ_i χ_Y with λ_i = G(d−i,s)/G(d,s). | pairing(Y, BC) = tr(YᵀBC) = ⟨B, YCᵀ⟩. Averaging over B gives [YCᵀ = 0], i.e. every row of C lies in the right kernel of Y, which has dimension d−i. The count is G(d−i,s), which is 0 when s > d−i. The transpose orientation checks. | Informal only | transport | Translate natively. |
| 15 | **Restricted adjoint.** ⟨TK, H⟩ = ⟨K, GH⟩ for invariant K. | The product bijection gives ⟨K, H(W restricted to its first c columns)⟩. Substituting W ↦ WU and using K(WU) = K(W) gives H(WR). Averaging over uniform U uses the R-marginal from step 12. Invariance is required only of the first argument; no unrestricted adjoint is claimed. | Informal only | transport | Translate natively. |
| 16 | **Cross-level orthogonality and exact energy.** | ⟨TP_iF, TP_jF⟩ = λ_j⟨P_iF, P_jF⟩. It is 0 for i ≠ j, which is also independently native in Full100 (`uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero`, which needs no invariance). It equals λ_i‖P_iF‖² for i = j. This agrees with step 8 through step 10: two independent routes give the same constant. | Mixed | transport | – |
| 17 | **Unchanged guarded contract.** | `spectral47_exact_contract_inhabitant` keeps every guard (h, ρ, parity, i ≤ d, ρ > 0, c/s splits, height cutoff ≤ h) in the statement without using them. 2^(−is) ≤ 2^(−i(s−1)) holds for all s, including s = 0, and the 3·2^(i−n) term is nonnegative. `SourceSizeContractBridge` is `Iff.rfl`. | Full101 frozen | transport | Native run plus a consumption trace. |

**Boundary cases I checked one by one:**
- **n = 0:** only the zero frequency exists. Levels i > 0 vanish, and λ₀ = 1.
- **c = 0:** G(0,i) = 0 for i > 0, and the second product vanishes too because d = s and d−i < s.
- **s = 0:** Φ is the identity, λ = 1, and the ratio is 1.
- **i = 0:** both products are empty, so equal to 1. P₀F is the constant mean.
- **i > c:** the numerator is zero and that branch is taken before dividing.
- **i > n:** there are no image subspaces, so both energies are 0.
- **i > d:** excluded by the contract, and empty in any case.
- **d = 0:** GL(0) is the trivial group.

All of these hold.

## 3. Complexity assessment

- **What the route is:** pure finite existence and counting over carriers of size 2^(nd) and |GL(d)| ≈ 0.29·2^(d²). It uses classical choices throughout: `Classical.choice` for in-fibre representatives, `propDecidable`, `Module.finBasis`, `LinearEquiv.ofFinrankEq`, `exists_rightInverse_of_surjective`, and the Classical.choice/Quot.sound/propext axiom profiles.
- **What it does not contain:**
  - no algorithm and no encoded witness;
  - no sampler for full-rank R, GL(d) or C, and no runtime or success-probability claim for such samplers;
  - no learning, reduction or selection procedure.
- **Distributions are identities, not procedures.** The uniform marginals and the independence of the new B from C are distributional identities only.
- **Spectral completeness does not imply hardness.** A complete spectral argument gives no hardness and no runtime witness.
- **Still open:** numeric NO; source/star/robust8S/pre-draw witnesses; physical sampling; the encoded runtime/reduction/learning debt; the upstream transports; and R14 HIGH.

## 4. Non-claims and evidence tiers

- **Full100 native GREEN** covers only its 327 captured sources and the 20 added requested axioms.
- **Full101** (11 sources) is frozen and has never been launched: there is no native acceptance.
- **The exact-energy candidate** and its Checks file sit outside Full101 and are uncompiled translations, not kernel evidence.
- **The operator-route steps 10–15** have no Lean source at all.
- **The Mathlib bodies** are read-only pinned text, with no fresh whole-package replay.
- **Attribution:** the spectral method belongs to MZ Lemma 4.7 and MZ24 Appendix A. The counts come from existing Mathlib (`card_linearIndependent`, `fintype_card_le_finrank`, and the dual/rank APIs).
- **Not claimed:** novelty or priority, any unconditional source or runtime result, a fresh-checkout replay, a full-340-body review, manuscript acceptance, or publication GO.
- **Still open:** the warnings, provider and final QA gates.

## 5. Verdicts

- **Argument sufficiency: SUFFICIENT, with no mathematical error found.**
  - This covers every exact manuscript equality: the exact energy ratio, the H-identity, the zero-factor conversion, the GL marginals, G T F = Φ F with independent unrestricted B, the kernel-frame eigenvalue, the restricted adjoint, cross-level orthogonality, and the exact squared norm.
  - It also proves the unchanged guarded inequality directly, not a weaker stand-in.
  - **Caveat:** the manuscript's text for Lemma 4.7 was not supplied, so I could not check that the manuscript statement matches word for word.
- **Candidate-native readiness: NOT READY.**
  - Full101 and the exact-energy candidate are uncompiled.
  - Steps 10–15 have not been translated.
  - Elaboration risks remain in steps 6 and 7.
- **Overall manuscript readiness: NOT READY / NO-GO.**

## 6. Remaining to-do list

1. Run Full101 natively: compile the 11 sources, collect axiom profiles, and trace their consumption into `spectral47_exact_contract_inhabitant`. Bind the Full100 covariance declarations.
2. Compile `ActualFiniteAppendExactImageEnergy` and run its Checks file (`#print axioms` on all three theorems).
3. Translate the remaining pieces natively:
   - the H-factorisation and the ℕ/ℝ zero-factor lemma;
   - the GL completion counts and both marginal pushforwards (R-forward, C via inversion);
   - the identity [MR B]U⁻¹ = M + (B − MS)C and the translation-independence step;
   - the definitions of G and Φ, and G T F = Φ F;
   - the kernel-frame eigenvalue, including its zero branch;
   - the restricted adjoint, invariance of P_iF, and the exact squared norm λ_i‖P_iF‖².
4. Prove natively that λ_i = G(c,i)/G(d,i), as a cross-check between the two routes.
5. Review the unsupplied imports and the standalone source-alignment audit. Finish the manuscript crosswalk against the actual MZ Lemma 4.7 / MZ24 Appendix A text, including that the row route replaces the duality prose.
6. Get independent native-body reviews of everything above.
7. Keep open: numeric NO; source/star/robust8S/pre-draw witnesses; sampling, runtime, reduction and learning; upstream transports; R14 HIGH; warnings and fresh-checkout certification; novelty, citations and PDF; and the provider/final QA and publication gates.
