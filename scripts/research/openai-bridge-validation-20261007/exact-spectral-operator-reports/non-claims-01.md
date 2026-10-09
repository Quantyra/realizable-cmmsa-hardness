# Non-claims review: exact spectral energy and operator route (E002 / S3137)

**This review is not final acceptance.** I used no tools, wrote nothing, and ran no Lean, Lake or subagents. Everything below comes from reading the supplied bodies and checking the mathematics by hand. That is not kernel evidence, and it does not upgrade any source to proof acceptance.

**Bottom line:**
- **The argument is mathematically sufficient.** I found no error. It proves the unchanged guarded Spectral47 inequality, and it proves every exact identity as the argument itself restates them.
- **It is not candidate-native ready.** The eleven Full101 sources have never been compiled, the exact-energy candidate is uncompiled, and the operator identities have no Lean translation yet.
- **It is not manuscript ready.** The manuscript text was not supplied, so I could not check the argument against it.

## 1. What I read and what I skipped

**Read in full (36 items):**
- **The argument** (SHA 153D21EC…) and the **Full100 native report** (4D580EA6…).
- **11 Full100-qualified project files:** `ActualFixedFunctionalAppendOperator`, `ActualAppendFourierCrossLevelOrthogonality`, `BinaryMatrixFourier`, `ActualSelectedComplementSourceSizeAnalyticMoment`, `ActualSelectedComplementAnalyticMoment`, `BinaryMatrixRightOrbit`, `BinaryMatrixRightFourierCovariance`, `BinaryMatrixSameRangeOrbit`, `MatrixLiftAffineTarget`, `SourceSizeContractBridge`, `GrassmannCounting`.
- **11 Full101 files (frozen, never launched):** `…Spectral47ExactInhabitant`, `…GlobalImageEnergy`, `…ImagePerImageEnergy`, `…ImageTailBridge`, `…FrameProductRatio`, `…BinaryImageOrbitFourier`, `…ImageWeighted`, `…BinaryImageFibres`, `…BinaryImageOrbit`, `…BinarySurjectionCounting`, `…AppendSpectral47`.
- **2 files outside Full101 (uncompiled):** `ActualFiniteAppendExactImageEnergy` and its `…Checks` file.
- **9 pinned Mathlib files:** `GeneralLinearGroup/Card`, `Dimension/Finite`, `Dual/Defs`, `Dual/Lemmas`, `Matrix/ToLin`, `Matrix/Rank`, `FieldTheory/Finiteness`, `Data/Matrix/Diagonal`, `Matrix/Trace`.

**Not supplied, so not reviewed:**
- **Manuscript and audits:** the MZ Lemma 4.7 and MZ24 Appendix A text; the source-alignment audit (52295A1A…); the 2197-case ratio audit; the earlier reviewer reports.
- **Project imports:** `ActualFixedFunctionalBinaryMatrixMoment` (which defines `coordinateArrayBinaryMatrixEquiv` and `rawTF`), `ActualRankImageRightBasisInvariance`, `ActualFiniteMomentLpBounds`, `ActualSelectedSpectralParameters`, the `…AppendMoment` modules, the `MatrixGrassmann*` and `MatrixLiftNominal*` modules, `GrassmannIncidence`, `MatrixGrassmannIntersectingAnchor`.
- **Other Mathlib modules:** Basis, Pi, Projection and the rest.

The Dual sources were read, but Full101 never uses them: it counts surjections through independent rows instead of through duality.

## 2. Step-by-step check

| # | Step | Sufficient? | Severity | What I checked | Required action |
|---|---|---|---|---|---|
| S1 | **Append coefficient identity**: coefficient of T g at Y equals coefficient of g at [Y 0] | Yes | — | Averaging over B sends χ_[Y W] to [W=0]·χ_Y. The native `appendAverage_character` proves this. Full101 proves the energy version over uniform B, including dependent and zero B. | Natively compile `appendAverage_rankProjection_energy_eq` |
| S2 | **Zero-tail block ↔ retained predicate** | Yes | — | `TailBridge` relates the matrix tail W, composition with the right injection, and the codRestricted surjection, in both directions. | Natively compile |
| S3 | **Matrices with image exactly S ↔ surjections onto S** | Yes | — | Both inverse laws hold. The map `i×d` sends independent rows to a surjection; the orientation is correct. Count is G(k,i) when i≤k. When i>k the type is empty (via `fintype_card_le_finrank`). i=0 gives exactly one map, including k=0. | Natively compile |
| S4 | **Retained fibre count G(c,i)** | Yes | — | `appendedZeroSurjectionEquiv` uses the decomposition x = inl(proj x) + inr(tail). Both inverse laws were checked. | Natively compile |
| S5 | **Coefficient is constant on each fixed-image fibre** | Yes | Low | Same image gives B·U = A (`exists_domain_equiv`). Checked: pairing(Y·Uᵀ, M) = pairing(Y, M·U), and the Wᵀ = U substitution. | Simplify: the native `fourierCoeff_eq_of_same_range` together with `fourierCoeff_rankProjection` already gives this (same image implies same rank), so the uncompiled rank-projection invariance route isn't needed here |
| S6 | **Grouping energies by image** | Yes | — | Empty fibres are handled without choosing a representative. i>n: no subspaces, so both sides are 0. c<i≤d: retained fibre is empty. | Natively compile |
| S7 | **Gain inequality and the contract** | Yes | Medium (warnings) | Each factor satisfies 2^s(2^c−2^j) ≤ 2^(c+s)−2^j, so the ratio is at most 2^(−is). Then 2^(−is) ≤ 2^(−i(s−1)), and adding 3·2^(i−n) ≥ 0 keeps it below the contract bound. All guards stay as binders; the bridge is `Iff.rfl`. | Unused names (`hEven hRho hc hs hHeight h rho`, and `basisInv` in `per_image_energy_ratio_of_empty`) will probably raise unused-variable warnings, which conflicts with the zero-warning gate. Rename them to `_…` |
| S8 | **H-product conversion** | Yes | Medium | For i≤c, G(c,i) = 2^(i(i−1)/2)·H(c)/H(c−i). Both ratios equal H(c)H(d−i)/(H(c−i)H(d)), using d−s = c and d−i−s = c−i (valid in ℕ only when i≤c). For c<i≤d, both have a zero factor: j=c in the first, j=d−i<s in the second. Denominators G(d,i) and G(d,s) are positive. | The ℕ→ℝ lemma must assume i≤d. For i>d, truncated ℕ subtraction gives d−i=0, while the real 2^(d−i)−1 is nonzero. Energies are 0 there, so equality still holds, but the conversion lemma itself fails without the guard |
| S9 | **G T F = Φ F** | Yes | Low | For fixed R the number of column completions is ∏_{j=c}^{d−1}(2^d−2^j), so R is uniform. U⁻¹ is uniform on GL(d). For fixed C the number of row completions is ∏_{j=s}^{d−1}(2^d−2^j), so C is uniform (the argument doesn't state this count; it should). Writing U⁻¹ = [A; C] gives RA + SC = I, so [MR B]U⁻¹ = M + (B−MS)C. Invariance is applied to U⁻¹. The shift B ↦ B−MS is a bijection, so (B′, U) is a uniform product. s=0 and c=0 both check. | Add the row-completion count; translate to Lean |
| S10 | **Kernel-frame eigenvalue** | Yes | — | ⟨Y, BC⟩ = ⟨Y·Cᵀ, B⟩, so averaging over B gives [Y·Cᵀ = 0], i.e. every row of C lies in ker Y (dimension d−i). λ_i = G(d−i,s)/G(d,s), which is 0 when s>d−i. No invariance is needed for this step. | Translate to Lean |
| S11 | **Restricted adjoint** | Yes | — | ⟨TK, H⟩ = E_W[K(W)·H(W first c columns)]. Reindex W ↦ WU (native `rightBasisEquiv`), use invariance of K, then the uniform R-marginal gives ⟨K, GH⟩. This is restricted to invariant first arguments; no unrestricted adjoint is claimed. | Translate; also P_jF invariance (`rankProjection_mul_right_eq` exists only in uncompiled Full101) |
| S12 | **Cross-level orthogonality and exact energy** | Yes | — | ⟨T P_iF, T P_jF⟩ = λ_j·δ_ij·‖P_iF‖². This matches S6 (the two routes agree algebraically). Cross-level orthogonality is already native in Full100, without invariance. | Natively compile the exact candidate and the operator route |

**Spot check.** I took n=c=s=i=1 with F(0)=a and F(≠0)=b. The full rank-1 energy is 3((a−b)/4)², the post-append energy is ((a−b)/4)², and both ratios equal 1/3.

**Boundary cases:**
- **n=0:** only rank 0 exists, and every energy for i>0 is zero.
- **c=0 or s=0:** handled as empty products.
- **i=0:** the empty product is 1.
- **i>c:** retained energy is zero.
- **i>n:** both energies are zero.
- **i>d:** excluded by the guard i≤c+s.
- **Normalizing cardinalities:** always 2^(nk) ≥ 1, never zero.

**Elaboration risks.** These are uncertainties, not errors, and only a native build can settle them:
- `heq_of_eq_cast` sigma reindexing.
- `simp … <;> funext j <;> rfl` in `appendedZeroSurjectionEquiv`.
- `simp` relying on `hEmpty` as a local instance.
- The `field_simp … <;> ring` chains.
- `simp_rw [hcoeff] at hglobal` rewriting under binders.
- The `rw [← parseval]` pattern match in the exact candidate.

## 3. Does the route prove the manuscript equalities?

As restated in the argument, it proves:
- the exact energy equality with λ_i;
- the s-factor product, including its zero branch;
- G T F = Φ F, with unrestricted B independent of full-row-rank C;
- the Φ-eigenvalue;
- the restricted adjoint and cross-level orthogonality.

It does this directly; it does not swap in an easier inequality. The guarded inequality follows with slack.

**Open alignment question (Medium).** The proof never needs the 3·2^(i−n) term or the rho, height and parity guards. Either the manuscript bound is loose for this operator, or the manuscript's sampler or operator differs from the unconditional append that the contract formalizes (for example, rank-conditioned appended columns). Without the manuscript text I can't say which. Until the crosswalk is done, this must stay recorded as "contract proven," not "MZ Lemma 4.7 proven."

## 4. Complexity

Everything here is finite existence and counting, using classical choice (`Classical.choose` preimages, `Fintype.ofFinite`, `LinearEquiv.ofFinrankEq`, `finBasis`). There is:
- **no algorithm or encoded witness;**
- **no sampler, selection, reduction or learning runtime.**

All of the following stay open: numeric NO, source, star and robust8S witnesses, pre-draw, physical sampling, reduction, runtime, upstream transports, and R14 HIGH. A complete spectral argument says nothing about hardness or runtime.

## 5. Evidence tiers and non-claims

**Native coverage is narrow.** Full100's native GREEN covers only its 327 captured sources. The report itself says `accepted:false`, `local_compilation:false`, `material_body_review_complete:false`, `consumption_trace_complete:false`, and `universal_Spectral47_inhabitant_proven:false`.

**Compilation status.** All eleven Full101 sources are uncompiled in this lineage. The two exact-energy files outside Full101 are uncompiled translations.

**Stale banners.** `GrassmannCounting` says "UNCOMPILED" and `BinaryMatrixRightOrbit` says "not native qualified," but both are listed as native. These banners are historical bytes; the report gives the actual status.

**Documentation drift.** The argument text counts through duality; the Lean counts through independent rows.

**Attribution.** The classical content belongs to MZ Lemma 4.7, MZ24 Appendix A, and Mathlib's `card_linearIndependent`, rank and dual results.

**What is not claimed:** novelty or priority, unconditional source or runtime results, fresh-checkout replay, review of all 340 bodies, manuscript acceptance, or publication GO. The warnings, provider and final QA gates remain open.

## 6. Verdicts

| Question | Verdict |
|---|---|
| Is the argument mathematically sufficient? | **Yes.** No error found. It covers the guarded inequality and all exact identities as restated. Alignment with the manuscript is unverified. |
| Is the candidate ready for native build? | **No.** Full101 is unlaunched, the exact candidate is uncompiled, the operator identities are untranslated, and there is likely warning debt. |
| Is the manuscript ready? | **No.** |

## 7. Remaining to-do list

1. Rename unused binders to `_`-prefixed names in the inhabitant and in `per_image_energy_ratio_of_empty`. Then build Full101 natively against the frozen dependency context, with axiom profiles, zero owned warnings, and exact source identities.
2. Natively compile `ActualFiniteAppendExactImageEnergy` and its checks.
3. Optionally reroute fibre constancy through the native `fourierCoeff_eq_of_same_range`.
4. Write the ℕ→ℝ product lemma (assuming i≤d) identifying the frame ratio with the manuscript's s-factor product, including its zero branch.
5. Translate to Lean:
   - the two GL completion counts (column ∏_{j=c}^{d−1} and row ∏_{j=s}^{d−1}) and both uniform marginals;
   - the translation identity [MR B]U⁻¹ = M + (B−MS)C, plus independence;
   - G T F = Φ F;
   - the kernel-frame eigenvalue;
   - the restricted adjoint;
   - exact energy through the operator route.
6. Get an independent body review of all of the above, plus the project and Mathlib imports I couldn't see.
7. Do the manuscript crosswalk: compare the MZ Lemma 4.7 and Appendix A sampler and operator against the unconditional-append contract, and explain why the 3·2^(i−n) term and the source guards are unnecessary.
8. Wire the SourceSize application through `spectral47_contract_iff` and complete the consumption trace.
9. Keep open: numeric NO; source, star, robust8S and pre-draw witnesses; sampling, selection, reduction, learning and runtime; upstream transports; R14 HIGH; warnings, fresh-checkout and provider/final QA; citations, PDF and publication gates.
