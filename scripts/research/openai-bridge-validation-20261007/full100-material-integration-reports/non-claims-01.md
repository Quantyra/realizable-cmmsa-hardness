# Full100 non-claims review: the two new bodies (`BinaryMatrixRightOrbit`, `BinaryMatrixRightFourierCovariance`) and the conditional material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **New declarations (8):** `same_range_matrix_right_orbit`, `basis_invariant_eq_of_same_range`, `rightBasisEquiv`, `pairing_mul_right`, `character_mul_right`, `uniformMean_comp_equiv`, `fourierCoeff_mul_right_of_basis_invariant`, `fourierCoeff_eq_of_same_range` | **Verified.** I found no soundness, direction, quantifier or vacuity defect. |
| **Conditional material integration** (192 roots, full192 and focused24 trace) | **GO-WITH-NOTES, conditional.** No HIGH is open in this scope. The new roots stand beside the material lane and do not feed it. |
| **The three input and body gaps** (Matrix/Rank, coordinate equivalence and append, alignment audit) | **Closed** for the questions asked. Details in §2. |
| **Unconditional material readiness** | **NO.** No universal Spectral47 inhabitant, no numeric NO bound, no joint witnesses. |
| **Overall GO** | **Not issued.** R14 (encoded reduction and runtime) is still an open HIGH, and the other full-scope gates are still open. |
| **Manuscript, Lemma 4.7 alignment, novelty, priority, publication** | **No acceptance.** |

**How I reviewed.** No tools, writes, Lean, Lake or subagents. I recomputed no hashes; every hash comparison is a string comparison between supplied values. Native, trace and custody facts are taken from the receipts. The argument and its three reviews are treated as proposals.

## 1. Coverage

| Body set | Count | Status |
|---|---|---|
| New: `BinaryMatrixRightOrbit.lean`, `BinaryMatrixRightFourierCovariance.lean` | 2 | **Read in full, every declaration.** |
| Pinned Mathlib: `Matrix/Rank`, `Matrix/ToLin`, `FieldTheory/Finiteness` | 3 | Read in full. I checked in detail only the declarations the new bodies and the argument rely on (listed in §2). |
| Prior project bodies, resupplied | 47 | Re-read at the interfaces the new bodies and the argument touch: `AppendOperator`, `AppendFourierCrossLevelOrthogonality`, `FixedFunctionalBinaryMatrixMoment`, `FiniteMomentLpBounds`, `SameRangeOrbit`, `MatrixLiftAffineTarget`, `SourceSizeContractBridge`, both `Spectral47ExactContract` definitions, and the export binders. Everything else is reused from the verified per-lens Full97, Full95 and Full90 reviews. |
| Complexitylib, resupplied | 23 | Supplied and unchanged. No new consumer; prior review reused. |
| Project bodies in the 327 closure that were not supplied | 278 | **Not reread.** Covered only by identity reuse: 8072 constant types and edges unchanged, and the configuration preserved. |
| External corpus | 409 | Pinned trust. Only the three Mathlib files above were supplied. |

**Skipped required fresh bodies: none.** The only new or changed bodies are the two read above (`changed_prior_bodies: []`).

**Still not supplied:**
- `BinaryMatrixFourier.lean`. It holds `pairing`, `character`, `fourier_parseval` and `fourierCoeff_rankProjection`. Its statements appear in the alignment audit, but its body is not supplied (finding NC100-7).
- `MatrixGrassmann*` and `ActualFixedFunctionalStarMoment`.

## 2. Input and body gaps the argument reviews left open

**`Matrix.rank` versus the `toLin'` range: closed.**
- `Rank.lean` defines `rank A := finrank R (LinearMap.range A.mulVecLin)`.
- `ToLin.lean` gives `Matrix.toLin'_apply' : toLin' M = M.mulVecLin`, by `rfl`.
- So `rank M = finrank (range (toLin' M))` holds definitionally.
- `range_toLin' M = span (range M.col)` and `rank_eq_finrank_span_cols` supply the column-space form.
- `rank_le_width` is the bound `rankProjection_finite_reconstruction` uses.
- `CommSemiring (ZMod 2)` holds, so nothing further is needed.

**The coordinate equivalence and append bodies are present: closed.**
- `coordinateArrayBinaryMatrixEquiv` is the explicit transpose, `A ↦ fun i j => A j i`, with both inverse laws holding by `rfl`.
- `appendBinaryMatrixEquiv` = prodCongr of the transposes ∘ `appendCoordinateArrayEquiv` (built on `finSumFinEquiv`, base columns first) ∘ transpose. Both inverse laws are proved.
- `appendBinaryMatrix_range_eq_span` and `appendBinaryMatrix_injective_iff` cover deficient arrays too.
- `appendAverage_character` and `character_appendBinaryMatrix` match their audited statements.

**The source alignment audit `52295A1A…F511` was inspected.**
- It lists 14 declarations across 6 paths, and the counts agree.
- Every statement whose body was supplied matches it token for token: `appendAverage`, `appendZeroFrequency`, `appendAverage_character`, `appendAverage_rankProjection_sum`, SourceSize `Spectral47ExactContract` (with `_`-prefixed binders), and the 2 + 2 new declarations.
- The audit's file hashes match the supplied headers for `AppendOperator` (EB71A55A), `AppendFourier` (AE8D620F), the SourceSize `AnalyticMoment` (03FB0A5D), `RightOrbit` (409FD652) and `RightFourierCovariance` (CF8990EA).
- I could not check line numbers or byte counts without tools.
- The five `BinaryMatrixFourier` statements are consistent with how they are used in the supplied bodies. For example, `FiniteMomentLp` unfolds `uniformMean` to sum/card, and `AppendFourier` unfolds `character` to `if pairing = 0 then 1 else -1`. They cannot be checked against a body.
- The audit itself records `mathematical_implication_reviewed: false`. I agree it is a statement-identity record, not an argument certificate.

**Still open and separate from these closures:**
- alignment with manuscript Lemma 4.7;
- the universal count, energy and gain proofs;
- the contract inhabitant;
- final acceptance.

## 3. Declaration audit

### `BinaryMatrixRightOrbit`

**`same_range_matrix_right_orbit`**
- **Input map.** It applies the generic lemma with `f = toLin' M`, `g = toLin' N`, `h : range f = range g`. This yields `e` with `N (e x) = M x`. The instances needed are `D = Fin d → ZMod 2` (finite-dimensional) and `C = Fin n → ZMod 2` (`Fintype`).
- **The matrices.** `U = toMatrix' e` and `V = toMatrix' e.symm`.
- **Inverse laws.** `toMatrix'_comp` gives `U*V = toMatrix'(e ∘ e.symm) = toMatrix' id = 1`. The same argument with the order reversed gives `V*U = 1`.
- **Orientation.** `toMatrix'` applied to `hcomp : (toLin' N) ∘ e = toLin' M` gives `toMatrix'(toLin' N) * toMatrix' e = M`, so `N * U = M` via `toMatrix'_toLin'`. This is a right action on the domain and agrees with the Full97 orientation.
- **Coverage.** There is no rank premise, so deficient maps, `N = 0`, `d = 0` and `n = 0` are all covered.

**`basis_invariant_eq_of_same_range`**
- `F M = F (N*U) = F N`, by `hInv N U V`. The codomain `A` is generic.
- It consumes invariance at every matrix and every paired-inverse `(U, V)`, which is exactly the shape of `_basisInv` in `Spectral47ExactContract` with `d = c+s`.

### `BinaryMatrixRightFourierCovariance`

**`rightBasisEquiv`**
- `(M*U)*V = M*(U*V) = M` and `(M*V)*U = M*(V*U) = M`. Both inverse laws hold.
- It acts on the complete carrier `BinaryMatrix n d`, so reindexing does not change normalization.

**`pairing_mul_right`**
- I re-derived it: `Σ_ij (YU)_ij M_ij = Σ_ik Y_ik Σ_j M_ij U_kj = Σ_ik Y_ik (MUᵀ)_ik`.
- The direction is `pairing(Y·U, M) = pairing(Y, M·Uᵀ)`.
- The proof's sum swap matches this derivation.

**`character_mul_right`** is immediate from `pairing_mul_right`.

**`uniformMean_comp_equiv`** is `Equiv.sum_comp` with the same denominator `card(BinaryMatrix n d)`.

**`fourierCoeff_mul_right_of_basis_invariant`**
- Transposes: `(VU)ᵀ = UᵀVᵀ = 1` and `(UV)ᵀ = VᵀUᵀ = 1`, both checked.
- `hInv` is applied at `(Uᵀ, Vᵀ)`, which is legitimate because `hInv` quantifies over all pairs.
- The resulting chain is `mean(F·χ_{YU}) = mean(F(MUᵀ)·χ_Y(MUᵀ)) = mean(F·χ_Y)`, reindexed by `M ↦ MUᵀ`. It is sound.

**`fourierCoeff_eq_of_same_range`** instantiates `basis_invariant_eq_of_same_range` at `fourierCoeff F`. This is sound: Fourier coefficients are constant on each column-space class, including the zero and deficient classes.

**Status.** Native GREEN covers these declarations, with standard profiles (`rightBasisEquiv` is a definition, also with a standard profile). This establishes the coefficient-constancy step only, not a universal Spectral47 inhabitant (`universal_Spectral47_inhabitant_proven: false`).

## 4. Status of the argument's remaining steps (for the actual operator, re-derived by me)

| Step | Status |
|---|---|
| Coefficient identity `fourierCoeff(appendAverage g, Y) = ĝ(appendZeroFrequency Y)` | **Sound on paper.** It uses `character_appendBinaryMatrix`, `χ_0 = 1`, and the product cardinality (`hcard` inside `FiniteMomentLp.appendAverage_lpMoment_le`). There is no extra normalization factor. **Not native.** |
| Zero-tail range and rank (`range [Y|0] = range Y`, including `s = 0`) | Sound via `range_toLin'` and a span-with-zero argument. **Not native.** |
| Rank-level Parseval, both energies | Sound given the audited `fourier_parseval` and `fourierCoeff_rankProjection`. **Not native.** |
| Recommended injection route: `full ≥ 2^{is}·post` | Sound for all n, c, s and i. `(Y, W) ↦ [Y|W]` is injective. When the columns of W lie in col(Y), `[Y|W]` has the same range and rank as `[Y|0]`, so `fourierCoeff_eq_of_same_range` applies, and `\|Ω_Y\| = 2^{is}`. Every empty or impossible branch is a vacuous sum. It keeps the same universal target. **Not native.** |
| rpow transfer: `2^{-is} ≤ 2^{-i(s-1)} + 3·2^{i-n}` | Sound, including `s = 0`. Every guard stays as an unused binder. **Not native.** |
| Fidelity of the contract to manuscript 4.7 | **Open.** The contract follows from invariance alone and leaves its guards and slack unused, so it may be weaker than 4.7. |

## 5. Integration (bytes unchanged, so the Full95 and Full97 checks carry forward)

- **Same objects throughout.** The same `I`, `copies`, `U`, `A`, `C`, `T` and `f` are used everywhere. One `Tc` serves `hfail`, the PR premise and the moment.
- **Source size.** `Instance N rows` keeps the source row count independent of the leaf count `m`. `c+s = 2h ≤ 2J`, with `hdim`, `hD` and `hsmall` derived.
- **HC46** is discharged by `original_HC46_exact`.
- **Dyadic exponent.** The caller chooses any dyadic `k ≥ 4m`.
- **Guards kept.** `hsel`, `hA`, `hrd`, `he`, `hfail`, `hSpectral` and `ha` are all retained.
- **Experiment not replaced.** The actual append experiment stands. It is not swapped for uniform or rank-one noise, and the source and star families are not narrowed.
- **The new modules are roots only.** No export consumes them, so `hSpectral` remains an explicit premise everywhere.
- **Selection.** Technical body selection being complete is different from the mathematical pre-draw source, selection and global-table witnesses, which stay open (`source_selection_complete: false`). The selected upstream profiles are not CMMSA bridges.

## 6. Custody and bookkeeping

**Typed records.**
- RightFourierCovariance: source CF8990EA…9E4B matches the header; object EFF637A8…B030 matches the legacy value.
- RightOrbit: source 409FD652…86B0 matches the header; object 79CC0A45…F06972 matches.
- The six earlier pairs are identical to Full97.
- No source value equals any object value.
- The legacy source-keyed field is read only as object hashes.
- The settled H1 category error is not reopened.

**Counts.**
- 172 + 20 = 192 roots.
- 325 + 2 = 327 sources.
- 8072 + 12 = 8084 trace nodes, consistent with 8 declarations plus auxiliaries. That is an inference; no per-node list was supplied.
- 2738 + 2 = 2740 external boundaries.

**Report hashes.** The hashes of the Full97 and argument reports cited in the reuse audit and the root reconciliation match the headers of the preserved reports. The reuse audit's old-index and old-graph hashes equal Full97's new ones.

**Info.** The instruction's figure of "661 actual compiled objects" does not appear in the supplied native report, which gives `cache_objects_unchanged: 566`. I cannot reconcile 661 from the packet; it is receipt-tier only.

## 7. Findings

| ID | Sev. | Declaration | Disposition and action |
|---|---|---|---|
| NC100-1 | Verified | `same_range_matrix_right_orbit` | Closes Full97 SR-2 / F97-4 (the missing matrix-form translation). |
| NC100-2 | Verified | `basis_invariant_eq_of_same_range` | None. |
| NC100-3 | Verified | `rightBasisEquiv`, `pairing_mul_right`, `character_mul_right`, `uniformMean_comp_equiv`, `fourierCoeff_mul_right_of_basis_invariant`, `fourierCoeff_eq_of_same_range` | Closes item (b) of CX97-02 and the covariance part of F97-3. |
| NC100-4 | Low (hygiene) | Header of `BinaryMatrixRightOrbit` | It says "not native qualified", which contradicts the GREEN receipt. Fix the docstring; the immutable captured bytes stay as they are. |
| NC100-5 | Medium (open) | Spectral47 chain | Still needed: the coefficient identity, the zero-tail rank lemma, the two Parseval energies, the injection count, the rpow transfer, and the guarded inhabitant transferred through `spectral47_contract_iff`. |
| NC100-6 | Medium (open; fidelity) | `Spectral47ExactContract` | Alignment with manuscript 4.7 is open. The provable bound is stronger and leaves the guards unused. Do not present that strengthening as novelty. |
| NC100-7 | Low (evidence tier) | `BinaryMatrixFourier` | Its body is not supplied. `pairing`, `character` and Parseval are credited through identity reuse plus how they are used. Supply the body for final review. |
| NC100-8 | Info | Count of 661 objects | Not reconcilable from the receipts. |
| Carried | Low | Stale banners in Dyadic and SourceSize `OriginalApplication`; legacy roots coupled to `m`; inherited warning debt | Unchanged. Owned and regression gates are zero, but total warnings are not. |
| Carried | Medium | Numeric NO, `hfail`/`e`, joint witnesses, source/star/robust8S, pre-draw table | Open. |
| R14 | **HIGH (outside scope)** | Encoded reduction and runtime | Open. Parameter size neither proves nor refutes it. **Bars overall GO.** |

## 8. Safe conditional claim

This rests on:
- pinned kernel and Init/Mathlib/Batteries trust;
- the Full100 qualified receipts: 192 standard profiles, seven stage exits of 0, and the 8084-node trace;
- the typed identities;
- identity reuse of the 325 prior bodies.

The claims:
- The SourceSize and Dyadic conditional material bounds from Full95 and Full97 stand unchanged.
- Any two binary matrices with equal `toLin'` range satisfy `N·U = M` for some pair `U, V` with `UV = VU = 1`.
- If a real function is invariant under all paired-inverse right actions, its Fourier coefficients are equal on equal-range frequencies.

**Not claimed:**
- universal Spectral47, or its alignment with Lemma 4.7;
- the HC46 contract applied as a Spectral47 substitute;
- a useful numeric NO bound, `hfail` or `e`;
- joint source, selector, star, robust8S or pre-draw-table witnesses;
- the physical sampler;
- encoded reduction, runtime or learning;
- exact upstream transports;
- warning-free or fresh-checkout certification;
- novelty, citations, PDF or publication;
- an unconditional theorem, priority, or manuscript acceptance.

## Remaining to-do

1. Prove natively the product-mean reindexing and `fourierCoeff(appendAverage g, Y) = ĝ(appendZeroFrequency Y)`.
2. Prove natively the matrix-form range lemma for `[Y|W]`, including the zero tail and `s = 0`, and the rank equalities.
3. Prove natively both rank-level Parseval energies.
4. Prove natively the injection inequality `2^{is}·post ≤ full`, including `|Ω_Y| = 2^{is}` via `card_eq_pow_finrank`.
5. Prove the rpow transfer, build `∀ cutoff, Spectral47ExactContract cutoff` with every guard kept, and transfer it through `spectral47_contract_iff`. Then run native gates, a fresh body review and a consumption trace through the original material exports.
6. Supply and review the `BinaryMatrixFourier` body.
7. Do the fidelity audit against manuscript Lemma 4.7.
8. Prove the HC46 and material consumer numerics: numeric NO, `hfail` at a useful `e`, the `B`/Parseval side conditions, `base` and `cutoff`, and an effective L₀.
9. Build the joint witness for `I`, `copies`, `U`, `A` and `hsel`; source/star/robust8S; the pre-draw global table; the physical sampler.
10. R14: encoded or implicit reduction and runtime; learning.
11. Upstream post-audit, then the CMMSA bridges.
12. Hygiene: the stale headers (including NC100-4), superseding the `m`-coupled roots, warnings and linter suppression, and a fresh-checkout replay with hash recomputation, which also resolves the 661 count.
13. Release: novelty and citation review, BibTeX and PDF QA, and the final full-scope providers.
