# Independent non-claims review: Full100 actual-append spectral image-fibre argument (E002 / S3137)

Scope: this is a review of the critical spectral argument only. It is not final acceptance and not a manuscript review. I used no tools, ran no Lean or Lake, made no writes and used no subagents.

## 1. Bodies inspected and skipped

**Inspected in full (supplied text):**
- `ActualFixedFunctionalAppendOperator`
- `ActualAppendFourierCrossLevelOrthogonality`
- `BinaryMatrixFourier`
- `ActualSelectedComplementSourceSizeAnalyticMoment`
- `ActualSelectedComplementAnalyticMoment` (legacy)
- `BinaryMatrixRightOrbit`
- `BinaryMatrixRightFourierCovariance`
- `BinaryMatrixSameRangeOrbit`
- `MatrixLiftAffineTarget`
- `SourceSizeContractBridge`
- Mathlib: `GeneralLinearGroup/Card`, `Dimension/Finite`, `Dual/Defs`, `Dual/Lemmas`, `Matrix/ToLin`

Five of the supplied source hashes match the report's `source_sha256`: AnalyticMoment, RightOrbit, RightFourierCovariance, SameRangeOrbit and ContractBridge.

**Skipped because they were not supplied. Their statements were taken as written and their bodies are unreviewed:**
- `ActualFixedFunctionalBinaryMatrixMoment`
- `ActualRankImageRightBasisInvariance`
- `ActualFiniteMomentLpBounds`
- `ActualSelectedComplementSourceSizeAppendMoment`
- `ActualSelectedSpectralParameters`
- `MatrixGrassmann*` and `MatrixLiftNominal*`
- Mathlib `Matrix/Rank`
- source-alignment audit `52295A1A…`, with its 6 identities and 14 declarations
- the 2197-case ratio audit
- the remaining closure sources

I could not check the argument packet hash `39AB07FC…`.

## 2. Target check

`Spectral47ExactContract cutoff` quantifies every `n c s h i`, `rho`, every real-valued `F` that is invariant under the full right action by paired inverses, and the guards `hEven`, `hi`, `hRho`, `hc`, `hs`, `hHeight`. Its conclusion is:

> E_M[(appendAverage (P_i F) M)²] ≤ (2^{−i(s−1)} + 3·2^{i−n}) · E_W[(P_i F W)²]

- **Operator:** `appendAverage` averages uniformly over all n×s matrices B, including zero and dependent ones. The base matrix M is uniform over all n×c matrices. The argument targets exactly this operator.
- **Guards:** a bound that holds with no guards inhabits the contract by taking the guards as binders and not using them. That is legitimate and removes no guard.
- **Bridge:** `spectral47_contract_iff` is `Iff.rfl`, so an inhabitant of either namespace transfers to the other.
- **Changed target:** none found between the argument and the Lean contract. I did not review whether the contract matches manuscript Lemma 4.7, because the alignment audit was not supplied. This stays open.

## 3. Step-by-step proof-adversarial findings

Each step below gives evidence, severity and disposition.

**S1. Fourier covariance direction**
- `pairing_mul_right`: Σᵢⱼ(YU)ᵢⱼMᵢⱼ = Σᵢₖ Yᵢₖ Σⱼ MᵢⱼUₖⱼ = ⟨Y, MUᵀ⟩. I re-derived this and it is correct.
- `fourierCoeff_mul_right_of_basis_invariant` uses invariance at (Uᵀ, Vᵀ). The paired-inverse identities come correctly from transposing VU=1 and UV=1, and the step reindexes through the bijection M↦MUᵀ.
- Severity: none. Sound, and native per the report.

**S2. Same-image coefficient constancy**
- `same_range_right_orbit` builds an automorphism e from the two range-restricted surjections. The kernels have equal finrank, by rank–nullity with equal range.
- From that, `same_range_matrix_right_orbit` gives N·U = M with U·V = V·U = 1. This covers deficient matrices, d=0 and n=0.
- Severity: none. Sound. The independent body review of the helper chain is still pending.

**S3. Coefficient identity: FourierCoeff(A_s g, Y) = FourierCoeff(g, [Y 0])**
- Re-derivation: χ_{[Y 0]}([M B]) = χ_Y(M)·χ_0(B) = χ_Y(M), using `character_appendBinaryMatrix`. So the left side equals E_M E_B g([M B])·χ_{[Y0]}([M B]).
- `appendBinaryMatrixEquiv` together with |Mat(n,c+s)| = |Mat(n,c)|·|Mat(n,s)| turns this into E_W g(W)χ_{[Y0]}(W).
- A second valid route: expand A_s g using `appendAverage_character`, then use uniqueness of coefficients.
- Severity: Medium as native debt only. It is not a mathematical gap. The packet is right that cross-level orthogonality alone does not give this.

**S4. Rank-level Parseval**
- With g = P_iF, `fourierCoeff_rankProjection` together with rank [Y 0] = rank Y gives post-append energy = Σ_{Y∈Mat(n,c), rk Y=i} f̂([Y0])².
- The full energy is the same identity applied directly.
- There is no stray normalisation factor: `uniformMean` uses the exact cardinality on each carrier.
- Severity: Low (debt). Sound.

**S5. Zero-tail image and rank**
- range [Y 0] = span(cols Y ∪ {0}) = range Y. This follows from `appendBinaryMatrix_range_eq_span` plus a span-union lemma. Equal rank follows from equal range.
- Severity: Low (debt). Sound.

**S6. Fixed-image count G(k,i) = ∏_{j<i}(2^k − 2^j)**
- Corestriction is a bijection with surjections Fᵏ→S, with both inverse laws holding by extensionality. Duality is a bijection with injections S\*→(Fᵏ)\*, and the frames route then gives the count. This is sound, including i=0, k=0 and the empty case i>k.
- **Repair recommendation (simplification, not a soundness fix):** the dual/bidual leg is unnecessary and carries extra obligations, including Finite/Fintype instances on spaces of linear maps and the naturality-of-evaluation inverse laws. A shorter route: fix a basis of S, so S ≃ F^i. Surjections Fᵏ→F^i correspond to i×k matrices A whose `toLin'` is surjective. That holds exactly when the rows of A are linearly independent, i.e. A is an independent i-frame in Fᵏ, which `card_linearIndependent` counts with hk : i ≤ k. The i>k branch is empty by `fintype_card_le_finrank`. In ℕ the product is also 0 there, since the j=k factor vanishes.
- Severity: Low.

**S7. Grouping by image and representative existence**
- The informal argument is sound. Representatives always exist: for any S with dim S = i ≤ d, G(d,i) > 0. The packet's caveat about absent fibres is correct but never actually triggers.
- **Recommended formulation, which avoids Grassmannian types and division:** double-count pairs (Y, Z′) with Y ∈ Mat(n,c), Z′ ∈ Mat(n,d), range Y = range Z′ and rank i. Using S2 and S5:

  > G(d,i) · post = G(c,i) · full, for every i.

  For any Z of rank i, i ≤ d holds automatically. So the fibre count only needs "#{Z : range Z = T} = G(k, finrank T)" for one submodule T at a time.
- Severity: Low.

**S8. Gain inequality**
- Per factor: 2^s(2^c − 2^j) = 2^{c+s} − 2^{s+j} ≤ 2^{c+s} − 2^j. Taking the product gives 2^{is}·G(c,i) ≤ G(d,i). This holds for all i, including i > c, where G(c,i) = 0.
- If rank-i matrices exist then G(d,i) > 0. Since the full energy is ≥ 0, post ≤ 2^{−is}·full. If i > d, both energies are 0.
- Then 2^{−is} ≤ 2^{−i(s−1)} because i ≥ 0, base 2 ≥ 1 and the real exponents are monotone. For s = 0 the right side is 2^i ≥ 1, which is fine. The 3·2^{i−n} term is nonnegative.
- Native cautions: casting truncated ℕ subtraction to ℝ needs 2^j ≤ 2^k, and the rpow-vs-npow conversion must be explicit.
- Severity: Low. Sound.

**S9. Original contract transfer**
- Sound as above. Note that `hi` is not needed either.
- Severity: none.

**Hidden assumptions:** I found none. F is an arbitrary real function, every carrier is a finite Fintype, and `rankProjection` uses `Matrix.rank`, which is finrank of range of `mulVecLin`, the same notion as range of `toLin'`.

**Hygiene:** `BinaryMatrixRightOrbit`'s header still says "not native qualified", which contradicts the GREEN report. This is a documentation fix only.

## 4. Complexity and non-claims audit

- The argument is a finite, nonconstructive identity plus an inequality for a universal Prop. It provides no algorithm, sampler, reduction, learning procedure or encoded runtime, and claims none. Under the complexity lens that debt stays open, and I am not asking for a substitute target.
- Counting novelty: `card_linearIndependent`, the dual APIs and the orbit/Fourier counting are classical results. No novelty should be claimed. The resulting ratio identity is standard Fourier analysis on Mat(n,d) under the GL_d action.
- Even after Spectral47 is inhabited, `selected_actual_material_moment_bound` stays conditional on `HC46ExactContract`, which is uninhabited, and on `hfail` and the selector. The report correctly has `universal_Spectral47_inhabitant_proven: false` and `numeric_NO_proven: false`.
- The 2197-case audit is consistent with the result but not evidence for it. The sharper bound (G(c,i)/G(d,i), with no 3·2^{i−n} term) should be reported as such and should not be read as resolving the manuscript's Lemma 4.7 alignment.

## 5. Verdicts

- **Argument sufficiency: SUFFICIENT.** I independently re-derived the whole argument and found no gap, hidden assumption or changed target relative to the Lean contract. The two recommended reformulations (rows-frame count; pairwise double counting with no division) are simplifications for native translation, not soundness repairs.
- **Native/final readiness: NOT READY.** The coefficient, Parseval, zero-tail, count, grouping, gain and inhabitant steps are untranslated. The consumption trace and fresh body review are pending.
- **Overall:** no GO, no manuscript acceptance, no unconditional hardness or priority claim.

## Remaining to-do list

1. Native: prove the coefficient identity FourierCoeff(appendAverage g, Y) = FourierCoeff(g, appendZeroFrequency Y) for the actual `appendBinaryMatrixEquiv`, including the product-cardinality mean.
2. Native: prove range and rank equality for `appendZeroFrequency`, i.e. range [Y 0] = range Y.
3. Native: prove the two rank-level Parseval energy identities with the rank filter.
4. Native: prove the fixed-range count #{Z ∈ Mat(n,k) : range Z = T} = ∏_{j<finrank T}(2^k − 2^j), both inverse laws included, via the recommended rows-frame route. Handle the i>k empty branch and the i=0/k=0 cases.
5. Native: prove the double-counting identity G(d,i)·post = G(c,i)·full.
6. Native: prove 2^{is}·G(c,i) ≤ G(d,i) in ℕ, then the real gain inequality with explicit cast/rpow lemmas and the i>d/i>c branches.
7. Native: build the `Spectral47ExactContract` inhabitant for all cutoffs, with every guard kept as a binder. Bind it to the exact source, dependency and axiom identities, and transfer it through `spectral47_contract_iff`.
8. Finish the exact consumption trace and fresh independent body review of all new declarations and the skipped dependencies, including `ActualRankImageRightBasisInvariance` and `ActualFiniteMomentLpBounds`.
9. Review the source-alignment audit `52295A1A…` and whether the contract matches manuscript Lemma 4.7.
10. Fix the stale "not native qualified" header in `BinaryMatrixRightOrbit`.
11. Still open beyond this argument: the `HC46ExactContract` inhabitant; numeric NO; source, star, robustness and pre-draw witnesses; physical sampling; encoded selection, runtime, reduction and learning; upstream bridges; warning and fresh-checkout certification; novelty and citations; PDF; publication; full-327 coverage and overall manuscript review.
