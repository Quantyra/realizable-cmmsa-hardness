# FULL100 complexity review: the two new matrix and Fourier bodies, and the full conditional material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **The two new bodies**: `BinaryMatrixRightOrbit` and `BinaryMatrixRightFourierCovariance` (8 declarations) | **Verified.** I found no defect in soundness, orientation, quantifiers, normalization or vacuity. |
| **Conditional material integration** (192 roots, exact-192 and focused-24 trace) | **GO-WITH-NOTES, conditional.** No HIGH finding is open in this scope. The material exports are byte-identical to Full95/97. The new roots run alongside them and do not feed into them. |
| **Spectral argument against the exact Lean contract** | **Sufficient**, and I re-derived it myself. Two of the input gaps the argument reviews named are now closed (§4). **Not native-ready.** |
| **Universal Spectral47 inhabitant** | **Open.** Neither new body constructs one. |
| **Unconditional material readiness** | **No.** |
| **Overall GO** | **Not issued.** R14, a HIGH finding on encoded reduction and runtime, is still open. Other full-scope gates are open too. |
| **Manuscript, Lemma 4.7 alignment, novelty, priority** | **No verdict, nothing accepted.** |

**Method.** I used no tools, wrote nothing, and ran no Lean, Lake or subagents. I recomputed no hashes; every hash comparison below is a string comparison against values in the packet. Compile results, axiom profiles, trace and custody come from the supplied receipts.

## 1. Coverage

| Body set | Count | Depth in this pass |
|---|---|---|
| **New:** `BinaryMatrixRightOrbit.lean` (409FD652…86B0) | 1 | Every declaration checked line by line |
| **New:** `BinaryMatrixRightFourierCovariance.lean` (CF8990EA…9E4B) | 1 | Every declaration checked line by line |
| **Mathlib:** `Matrix/Rank`, `Matrix/ToLin`, `FieldTheory/Finiteness` | 3 | Read in full. The declarations used are listed in §4. |
| **Prior project bodies, fresh interface re-check:** `BinaryMatrixSameRangeOrbit`, `MatrixLiftAffineTarget` (`splitSurjection`, `surjective_target_orbit`), `ActualRankImageRightBasisInvariance` (imported by RightOrbit), `ActualFixedFunctionalAppendOperator` (`appendBinaryMatrixEquiv`, `appendAverage`, `appendBinaryMatrix_range_eq_span`), `ActualFixedFunctionalBinaryMatrixMoment` (`coordinateArrayBinaryMatrixEquiv`), `ActualAppendFourierCrossLevelOrthogonality` (`character_appendBinaryMatrix`, `appendAverage_character`), `ActualFiniteMomentLpBounds` (product-mean reindexing), both SourceSize contract definitions, `SourceSizeContractBridge` | 10 of the 47 | Re-checked at the interfaces the Spectral47 route consumes |
| **Other supplied prior bodies** (37 project, 23 Complexitylib) | 60 | Present and unchanged. Credit comes from prior per-lens review, matched by identity. I am not claiming a fresh line-by-line re-read. |
| **Unsupplied project bodies** (327 − 49 supplied), including `BinaryMatrixFourier` | 278 | Identity reuse only: 8072 shared constants, types and edges unchanged, configuration preserved |
| **Unsupplied external files** | about 383 | Pinned trust only. This assumes the three Mathlib files belong to the 409-file index. |

**Skipped required fresh bodies: none.** `changed_prior_bodies` is empty, and both new or changed bodies were read in full.

`BinaryMatrixFourier` is not supplied in this packet. For `pairing`, `character`, `uniformMean`, `fourierCoeff`, `rankProjection`, `fourier_parseval` and `fourierCoeff_rankProjection` I rely on the statements quoted in the alignment audit. The double-sum shape of `pairing` is also confirmed at kernel level, because `pairing_mul_right` unfolds it and compiles.

## 2. New declarations

### `BinaryMatrixRightOrbit`

**`same_range_matrix_right_orbit`: Verified.**
- It instantiates `same_range_right_orbit` with `f := toLin' M` and `g := toLin' N`, giving `e` with `toLin' N (e x) = toLin' M x`.
- It sets `U := toMatrix' e` and `V := toMatrix' e.symm`.
- **`U*V = 1`.** Rewriting `← toMatrix'_comp` turns `toMatrix' e * toMatrix' e.symm` into `toMatrix'(e ∘ e.symm)`. Then `huv` reduces that to `toMatrix' id`, which is `1`. The multiplication order matches `toMatrix'_comp : toMatrix'(f.comp g) = toMatrix' f * toMatrix' g`. `V*U = 1` follows symmetrically.
- **`N*U = M`.** `toMatrix'` applied to `(toLin' N).comp e = toLin' M`, then `toMatrix'_comp` and `toMatrix'_toLin'`, gives `N * U = M`. The orientation is correct: the right factor acts on domain coordinates.
- **Edge cases.** No rank or injectivity premise is used, so deficient, zero, `n = 0` and `d = 0` cases are all covered. The generic lemma's `[FiniteDimensional]` and `[Fintype C]` requirements hold for `Fin d → ZMod 2` and `Fin n → ZMod 2`.

**`basis_invariant_eq_of_same_range`: Verified.** The chain is `F M = F (N*U) = F N`, using `hInv N U V hUV hVU`. It works for any codomain `A`.

### `BinaryMatrixRightFourierCovariance`

**`rightBasisEquiv`: Verified.** Both inverse laws hold by associativity: `(MU)V = M(UV) = M` and `(MV)U = M(VU) = M`. It is a genuine bijection of the whole carrier, including deficient matrices.

**`pairing_mul_right`: Verified.** The transpose direction is correct:
- Σ_j (Σ_k Y_ik U_kj) M_ij = Σ_k Y_ik Σ_j M_ij U_kj
- = Σ_k Y_ik (M Uᵀ)_ik
- So `pairing(YU, M) = pairing(Y, M Uᵀ)`. The `ring` step is valid because ZMod 2 is commutative.

**`character_mul_right`: Verified.** It is a direct rewrite.

**`uniformMean_comp_equiv`: Verified.** Reindexing stays on the same carrier, so the `card` normalization is unchanged automatically.

**`fourierCoeff_mul_right_of_basis_invariant`: Verified.**
- `UᵀVᵀ = (VU)ᵀ = 1` and `VᵀUᵀ = (UV)ᵀ = 1`, both via `transpose_mul`. The roles are correctly swapped.
- `hInv` is used at `(M, Uᵀ, Vᵀ)`, for every `M`.
- The reindex `M ↦ MUᵀ` is `rightBasisEquiv`. No extra factor appears.

**`fourierCoeff_eq_of_same_range`: Verified.** It applies `basis_invariant_eq_of_same_range` to `Y ↦ fourierCoeff F Y`, using the previous lemma as the invariance hypothesis.

**What these declarations do and do not establish.** They give constancy of the coefficients on same-range classes, in one direction only. They contain no converse, no class or fibre count, no append coefficient identity, no energy identity, no gain bound and no Spectral47 inhabitant. The file header says this correctly.

## 3. Typed custody and bookkeeping

- **Typed identities.** For RightOrbit, source 409FD652…86B0 pairs with object 79CC0A45…F06972. For RightFourierCovariance, source CF8990EA…9E4B pairs with object EFF637A8…B1030.
  - In both cases the source hash matches the file header, and the object hash matches the legacy `added_object_hashes` value.
  - The other six pairs are unchanged from Full97.
  - No source hash equals any object hash. The settled H1 category error stays closed.
- **Roots.** 172 + 20 = 192. Equivalently 184 + 8, where the 8 are exactly the 8 new declarations.
- **Focused trace.** 16 + 8 = 24.
- **Sources.** 325 + 2 = 327.
- **Nodes.** 8072 + 12 = 8084. That is consistent with 8 roots plus auxiliary nodes, for example the compiled proof fields of `rightBasisEquiv`. This is an inference; no per-node enumeration was supplied.
- **External boundaries.** 2738 + 2 = 2740. That is plausible for newly reached Mathlib matrix and transpose constants, but it is also unenumerated.

## 4. Input gaps from the argument reviews

**Rank equals the finrank of the `toLin'` range: closed.**
- `Matrix.rank A := finrank R (LinearMap.range A.mulVecLin)` (Rank.lean).
- `Matrix.toLin'_apply' : toLin' M = M.mulVecLin`, which holds by `rfl` (ToLin.lean).
- `range_toLin'` and `rank_eq_finrank_span_cols` give the column-span form.
- So equal ranges imply equal ranks, and the rank filter in `rankProjection` is the same notion used by the orbit lemma.

**`coordinateArrayBinaryMatrixEquiv` and the append definitions: closed.**
- `coordinateArrayBinaryMatrixEquiv` is the column transpose, `toFun A = fun i j => A j i`.
- `appendBinaryMatrixEquiv` puts the base columns first, via `finSumFinEquiv`.
- `appendBinaryMatrix_apply_castAdd` and `appendBinaryMatrix_apply_natAdd` give the entrywise reading.
- The product-mean reindexing that the coefficient identity needs already appears inside the proof of `ActualFiniteMomentLpBounds.appendAverage_lpMoment_le` (`hcard`, `hsum'`). It can be extracted as a standalone lemma.

**Source alignment audit 52295A1A…F511: reviewed.**
- The quoted statements agree with the supplied bodies for `appendAverage`, `appendZeroFrequency`, `appendAverage_character`, `appendAverage_rankProjection_sum`, `Spectral47ExactContract` (the SourceSize version with underscored guards) and all four RightOrbit and Covariance statements. The file hashes match the headers.
- I cannot verify the `BinaryMatrixFourier` statements (body not supplied) or any line numbers.
- Its `required_remaining_proofs` list includes a "frame pushforward / dual-frame fibre equivalence". That obligation goes away if the injection route below is adopted.
- The audit's own `mathematical_implication_reviewed: false` is correct, and closing input gaps does not change it.

**Still open:**
- alignment with manuscript Lemma 4.7;
- every native transport;
- the universal count, energy and gain proofs, and the contract proof;
- final acceptance.

## 5. Spectral47 route against the exact contract (re-derived; translation guidance)

I recommend the injection route, which keeps the same universal target and all guards. Write ĝ for the Fourier coefficient of g, and Ω_Y for the set of W ∈ Mat(n,s) whose columns all lie in range Y.

1. **Coefficient identity.** `fourierCoeff (appendAverage g) Y = fourierCoeff g (appendBinaryMatrix Y 0)`. This follows from `character_appendBinaryMatrix` together with χ₀ = 1 (proved inside `appendAverage_character`) and the product-mean reindex.
2. **Range of an appended block.** If every column of W lies in range Y, then range [Y W] = range Y. This uses `appendBinaryMatrix_range_eq_span` plus a span-union lemma. The case W = 0 is the zero-tail lemma, and the case s = 0 needs no special handling.
3. **Size of Ω_Y.** |Ω_Y| = (2^{rank Y})^s, by `Module.card_eq_pow_finrank` from Finiteness.lean.
4. **Injectivity.** `(Y, W) ↦ [Y W]` is injective because `appendBinaryMatrixEquiv` is an equivalence.
5. **Gain bound.** Use `fourier_parseval` and `fourierCoeff_rankProjection` on both carriers, with constancy applied to F̂ (F itself is invariant, so P_iF does not need to be). This gives
   - full ≥ Σ_{rank Y = i} Σ_{W ∈ Ω_Y} F̂([Y W])² = 2^{is} · post.
   - The bound is multiplicative and needs no division. The cases i > c, i > d, i > n, i = 0 and zero dimensions all reduce to empty sums or equalities.
6. **Exponent comparison.** 2^{−is} ≤ 2^{−i(s−1)}, using `Real.rpow_le_rpow_of_exponent_le` and `rpow_natCast`/`rpow_neg`. The term 3·2^{i−n} is nonnegative.
7. **Contract inhabitant.** Take every guard as a binder, prove `∀ cutoff, Spectral47ExactContract cutoff`, and transfer it through `spectral47_contract_iff`.

**Fidelity caveat (carried).** This route never uses ρ, `hHeight`, parity, `hc`, `hs` or the 3·2^{i−n} slack. The formal contract is therefore weaker than what is provable, and its relation to manuscript Lemma 4.7 is unverified. Proving the contract would discharge `hSpectral` in the exports. It would not certify the manuscript lemma.

## 6. Conditional material integration (re-confirmed, bytes unchanged)

- **Same objects.** I, copies, U, A, C, T and f are the same throughout. The same `Tc` appears in `hfail`, in the PR premise and in the moment. The same `Cc`/`fc` appear in the center identity.
- **Row count.** `Instance N rows` keeps the source row count independent of the leaf count `m`.
- **Dimensions.** c + s = 2h ≤ 2J. `hdim`, `hD` and `hsmall` are derived.
- **HC46.** `original_HC46_exact` is applied through the universal contract at `hEven := hsplit`.
- **Dyadic exponent.** The caller chooses k ≥ 4m, and `hklt` was soundly removed.
- **Guards kept.** `hsel`, `hA`, `hrd`, `he`, `hfail`, `hSpectral` and `ha` are all still present.
- **Experiment not replaced.** The append experiment is not swapped for uniform or rank-one noise, and the source and star family is not narrowed.
- **Selection scope.** Technical selection of source bodies is complete. The mathematical pre-draw source, selection and global-table witnesses remain open (`source_selection_complete: false`).

## 7. Findings

| ID | Severity | Declaration | Evidence | Disposition and action |
|---|---|---|---|---|
| CX100-01 | Verified | `same_range_matrix_right_orbit` | §2: `toMatrix'_comp` orientation, both inverse laws, `N*U = M` | Credit it as a matrix-form orbit lemma |
| CX100-02 | Verified | `basis_invariant_eq_of_same_range` | §2 | None |
| CX100-03 | Verified | `rightBasisEquiv`, `uniformMean_comp_equiv` | §2: both inverse laws, same-carrier normalization | None |
| CX100-04 | Verified | `pairing_mul_right`, `character_mul_right` | Transpose direction re-derived | None |
| CX100-05 | Verified | `fourierCoeff_mul_right_of_basis_invariant`, `fourierCoeff_eq_of_same_range` | Transposed inverse pair; uses `hInv` over all M | Credit as one-directional constancy only |
| CX100-06 | Info, closes an input gap | rank ↔ `toLin'` range | Rank.lean definition plus `toLin'_apply'` (`rfl`) | Closed |
| CX100-07 | Info, closes an input gap | coordinate and append definitions | Transpose; base columns first; product-mean template in `FiniteMomentLpBounds` | Closed. Extract the reindex lemma. |
| CX100-08 | Low | Alignment audit | Statements consistent; Fourier body and line numbers unverified; one remaining-proof item unnecessary | Supply the Fourier body for re-check, or accept identity reuse; update the obligation list |
| CX100-09 | Low (stale) | `BinaryMatrixRightOrbit` header ("not native qualified") | Contradicted by the native receipt | Historical bytes, so leave the immutable input as is; fix in the next revision |
| CX100-10 | Medium, open | Spectral47 inhabitant | §5, steps 1–7 not yet native | Translate natively, then run an independent body review and an exact trace |
| CX100-11 | Low, open | Contract fidelity to Lemma 4.7 | Guards unused; manuscript text not supplied | Fidelity audit |
| CX100-12 | Low (evidence tier) | Trace +12 nodes / +2 boundaries | Not enumerated | Per-node enumeration during fresh-checkout replay |
| Carried | Low | Legacy source-keyed object field; ID-2 seal members; stale banners in Dyadic and SourceSize; m-coupled legacy roots; inherited warning and linter debt | Unchanged | Hygiene |
| Carried | Medium, open | Numeric NO and a useful `e`/`hfail`; joint source/selector/copies/U/A witness; source, star, robust8S and pre-draw table; physical sampler | Unchanged | See the to-do list |
| **R14** | **HIGH, open** (outside the material scope) | Encoded reduction and runtime (doubly exponential J) | No implicit encoding and no runtime theorem. Parameter size alone neither proves nor disproves this. | **Bars overall GO** |

## 8. Safe conditional claim

This rests on pinned kernel and Init/Mathlib/Batteries trust, the qualified FULL100 receipts (192 standard profiles, seven stage exits of 0, 327 sources, 8084/8084 exact type edges), the typed source/object identities, and identity reuse of the 325 prior bodies. Under those assumptions:

- **Prior claims stand.** The Full95/97 SourceSize and Dyadic material bounds hold unchanged, with HC46 discharged and Spectral47 kept as an explicit premise.
- **Matrix orbit.** If two binary matrices `M` and `N` have the same `toLin'` range, then `N·U = M` for some paired-inverse `U` and `V`. Any function invariant under paired-inverse right multiplication of all matrices takes equal values on matrices with the same range.
- **Fourier constancy.** For such an invariant real `F`, `F̂(Y·U) = F̂(Y)`, and F̂ is constant on each same-range class.

**Not claimed:**
- universal Spectral47 or its fidelity to Lemma 4.7;
- any class count, append coefficient or energy identity;
- a numeric NO bound, a useful `e`/`hfail`, or joint witnesses;
- source, star, robust8S or the pre-draw table, or the physical sampler;
- encoded reduction, runtime or learning;
- upstream or CMMSA bridges;
- zero total warnings or fresh-checkout certification;
- novelty, citations, PDF or publication;
- overall GO, any unconditional theorem, or manuscript acceptance.

## Remaining to-do

1. **Native Spectral47** via the injection route:
   - a product-mean reindex lemma;
   - `fourierCoeff (appendAverage g) Y = fourierCoeff g [Y 0]`;
   - range [Y W] = range Y for every W ∈ Ω_Y;
   - |Ω_Y| = 2^{is};
   - injectivity of `(Y, W) ↦ [Y W]`;
   - the rank-level Parseval energy identities;
   - the gain bound 2^{is} · post ≤ full, then the rpow transfer;
   - `∀ cutoff, Spectral47ExactContract cutoff` with all guard binders, transferred through `spectral47_contract_iff`.
2. **Qualify those declarations natively.** Bind their source and object identities, run an independent body review of every new declaration, and run an exact consumption trace through the original and Dyadic exports.
3. **Fidelity audit** of `Spectral47ExactContract` against manuscript Lemma 4.7, and settle on one canonical contract constant.
4. **Numeric NO.** Certify the scalar consumer: choose r, T and dyadic P; prove Parseval ΣE ≤ 1; instantiate `base` and `cutoff` (h > 20000m³); give an effective L₀; prove `hfail` at a useful `e`; compare against the actual selection threshold.
5. **Joint witness** for I (rows ≥ 1), padded copies, U, A, C, T, f and `hsel`.
6. **Source and star.** Acceptance → fixed f; `AllAmbientInverse`/robust8S; the pre-draw global table; the physical sampler; `kappa`/`hexpand`; completeness 1 − η.
7. **R14.** Encoded or implicit reduction with a runtime proof, explicit expander tables and `rotVal` cost; learning.
8. **Upstream.** Post-audit, then the exact CMMSA bridges.
9. **Custody and hygiene:**
   - recompute every source and object hash from the custody archives during fresh-checkout replay;
   - provide seal-member listings and per-node trace enumeration;
   - retire the legacy object field;
   - fix stale banners, including the RightOrbit header, in the next revision;
   - mark the m-coupled roots as superseded;
   - dispose of the inherited warning and linter debt.
10. **Release.** Manuscript fidelity, novelty and citation review, BibTeX and PDF QA, and the final full-scope providers.
