# Full100 proof-adversarial review: the two new bodies (`BinaryMatrixRightOrbit`, `BinaryMatrixRightFourierCovariance`) and conditional material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **The two new bodies, all 8 declarations** | **Verified.** I found no soundness, orientation, quantifier, normalization or vacuity defect. |
| **Native and conditional material integration**: 192 roots, the exact-192 and focused-24 traces, the SourceSize/HC46/Dyadic exports | **GO-WITH-NOTES, conditional.** No HIGH is open in this scope. The material exports have the same bytes and object hashes as before, so the earlier conditional verdict carries forward unchanged. |
| **Unconditional material readiness** | **No.** Spectral47 is still an explicit premise of every export. There is no universal inhabitant yet. |
| **Overall GO** | **Not issued.** R14 (encoded reduction/runtime) is still an open HIGH. The other full-scope gates are also open. |
| **Manuscript, priority, unconditional theorem** | No verdict. Nothing is accepted. |

**How I reviewed.** I used no tools, made no writes, and ran no Lean, Lake or subagents. Every hash comparison below is a string comparison of values in the packet; I recomputed none. Native, profile, trace and custody facts come from the receipts.

## 1. Coverage

| Body set | Status in this pass |
|---|---|
| `BinaryMatrixRightOrbit.lean` (new, 409FD652…) | **Read line by line.** Both declarations re-derived. |
| `BinaryMatrixRightFourierCovariance.lean` (new, CF8990EA…) | **Read line by line.** All 6 declarations re-derived. |
| Mathlib `Matrix/Rank.lean` (4CE45784…) | **Read in full.** I re-derived the declarations used here: `rank` def, `rank_eq_finrank_span_cols`, `rank_le_width`. The rest are pinned trust only. |
| Mathlib `Matrix/ToLin.lean` (9AEFBF5B…) | **Read in full.** Re-derived: `toLin'_apply'` (rfl), `toMatrix'_comp`, `toMatrix'_toLin'`, `toMatrix'_id`, `range_toLin'`, `toLin'_mul`. |
| Mathlib `FieldTheory/Finiteness.lean` (05316F2A…) | **Read in full.** Used: `Module.card_eq_pow_finrank`. |
| Supplied prior bodies re-read fresh at the new interfaces | `ActualFixedFunctionalBinaryMatrixMoment`, `ActualFixedFunctionalAppendOperator`, `ActualAppendFourierCrossLevelOrthogonality`, `ActualFiniteMomentLpBounds`, `ActualRankImageRightBasisInvariance`, `BinaryMatrixSameRangeOrbit`, `MatrixLiftAffineTarget` (`surjective_target_orbit`, `splitSurjection`), the SourceSize contract plus `SourceSizeContractBridge`. |
| The other supplied prior bodies (about 38 project, 23 Complexitylib) | Supplied and byte-identical (`changed_prior_bodies: []`). I checked them only at interfaces. **Their coverage is inherited** from the Full95/Full97 per-lens reviews by identity; I am not claiming a fresh line-by-line reread. |
| Unsupplied bodies (280 project, the external closure) | Identity reuse only (8072 shared constant types/edges unchanged), or pinned trust. Not reread. |

**Skipped required fresh bodies: none.** The only new or changed bodies are the two listed first, and I read both completely.

**One unsupplied dependency matters semantically:** `BinaryMatrixFourier` (`pairing`, `character`, `uniformMean`, `fourierCoeff`, `rankProjection`, `fourier_parseval`, `character_orthogonality`). I take its statements from the alignment audit and the compiled call sites. Its body is covered by identity reuse only (see ALN-2).

## 2. `BinaryMatrixRightOrbit`

**`same_range_matrix_right_orbit` (M N, equal `range (toLin' ·)`): there exist U, V with `U*V=1`, `V*U=1`, `N*U=M`.**
- **Instantiation.** It instantiates `same_range_right_orbit` at `D = Fin d → ZMod 2` and `C = Fin n → ZMod 2`. Both instances (`FiniteDimensional`, `Fintype`) hold, so the generic Full97 lemma is genuinely consumed.
- **Matrices.** `U := toMatrix' e` and `V := toMatrix' e.symm`.
- **`U*V = 1`.** `toMatrix'_comp` gives `toMatrix'(f ∘ g) = toMatrix' f * toMatrix' g`. So `U*V = toMatrix'(e ∘ e.symm) = toMatrix' id = 1`. `V*U` is symmetric. Both inverse laws are proved; neither is assumed.
- **Orientation.** `he : toLin' N (e x) = toLin' M x` gives `(toLin' N) ∘ e = toLin' M`. Applying `toMatrix'` and `toMatrix'_toLin'` gives `N * U = M`. The right action is on the domain, which is what `basisInv` (`F (M*U) = F M`) consumes.
- **No rank hypothesis.** Rank-deficient and zero matrices are covered.
- **Degenerate sizes.** `d = 0`: U and V are the unique 0×0 matrix. `n = 0`: `C` is a singleton and the generic lemma still applies.

**`basis_invariant_eq_of_same_range`.** `F M = F (N*U) = F N` via `hInv N U V`. This is correct for an arbitrary codomain `A`.

## 3. `BinaryMatrixRightFourierCovariance`

| Declaration | Check |
|---|---|
| `rightBasisEquiv` | `(M U) V = M(UV) = M` and `(M V) U = M(VU) = M`. Both inverse laws use the stated hypotheses. It is a bijection on the full matrix carrier, with no rank filter. |
| `pairing_mul_right` | Σⱼ(Σₖ Y_ik U_kj) M_ij = Σₖ Y_ik Σⱼ M_ij U_kj = Σₖ Y_ik (M Uᵀ)_ik. So **pairing(YU, M) = pairing(Y, MUᵀ)**: the transpose lands on the data, not the frequency. This is correct, and over ZMod 2 the `ring` step is sound. |
| `character_mul_right` | Immediate by unfolding. |
| `uniformMean_comp_equiv` | Same carrier on both sides, so the denominator is unchanged; `Equiv.sum_comp` reindexes the numerator. No normalization factor changes. |
| `fourierCoeff_mul_right_of_basis_invariant` | Transposing `VU=1` gives `UᵀVᵀ=1`, and transposing `UV=1` gives `VᵀUᵀ=1` (using `transpose_mul`). `hInv` is applied at `(Uᵀ, Vᵀ)`. The pointwise rewrite is `F M · χ_{YU}(M) = F(MUᵀ) · χ_Y(MUᵀ)`, followed by reindexing by `M ↦ MUᵀ`. The direction is correct. |
| `fourierCoeff_eq_of_same_range` | Applies `basis_invariant_eq_of_same_range` to `fourierCoeff F`. The `hInv` binder has exactly the shape of `Spectral47ExactContract._basisInv`: same binder order, all matrices, paired inverses. So `fourierCoeff_eq_of_same_range F _basisInv` is directly usable inside a future inhabitant. |

## 4. Input gaps closed by this packet

**Rank equals the finrank of the `toLin'` range (MR-1).** In `Rank.lean`, `rank A := finrank (range A.mulVecLin)`. In `ToLin.lean`, `toLin' M = M.mulVecLin` holds by `rfl` (`toLin'_apply'`). Therefore `Matrix.rank Y = finrank (range (toLin' Y))`, and equal ranges imply equal rank, as used by the `rankProjection` filter.

**Coordinate equivalence and append orientation (CE-1).**
- `coordinateArrayBinaryMatrixEquiv` maps A to `fun i j => A j i`. So column j of the matrix is A j: arrays are columns.
- `appendBinaryMatrix M B` places M's columns first, then B's. This is pinned by `appendBinaryMatrix_apply_castAdd` and `appendBinaryMatrix_apply_natAdd`.
- `character_appendBinaryMatrix` pairs the frequency blocks in that same order.
- `appendBinaryMatrix_range_eq_span` gives `range = span(range (concatenate M B))`. So `range [Y | 0] = range Y`; with s = 0 the tail is empty.
- **Translation debt (Low):** that lemma is stated for coordinate-array inputs. Applying it to an arbitrary `BinaryMatrix` needs one rewrite through the equivalence.

**Product-mean cardinality (CN-1).** `|Mat(n,c+s)| = |Mat(n,c)| · |Mat(n,s)|` follows from `Fintype.card_congr appendBinaryMatrixEquiv`; this already appears inside the proof of `appendAverage_lpMoment_le`. It is not exported as a standalone lemma.

**Alignment audit 52295A1A… (ALN-1, ALN-2).**
- Every listed statement whose body is supplied matches that body exactly: `appendAverage`, `appendZeroFrequency`, `appendAverage_character`, `appendAverage_rankProjection_sum`, `Spectral47ExactContract`, and the 4 new-file declarations.
- The `BinaryMatrixFourier` statements match how they are used, but their bodies are identity-reused only (ALN-2).
- The audit's flag `mathematical_implication_reviewed: false` is now answered by §5. That answer is review, not certification.

## 5. Spectral47 route against the supplied sources (review only, not native)

1. **Coefficient identity.** By `character_appendBinaryMatrix` with χ₀ = 1 and the product cardinality, the Fourier coefficient of A_s g at Y equals ĝ([Y | 0]).
2. **Post-append energy.** With g = P_i F, Parseval on Mat(n,c) gives post = Σ_{rank Y = i} F̂([Y | 0])². Here `rank [Y | 0] = rank Y` by CE-1 and MR-1.
3. **Full energy.** full = Σ_{rank Z = i} F̂(Z)².
4. **Injection route.** Let Ω_Y be the set of W whose columns lie in col(Y).
   - |Ω_Y| = (2^i)^s, by `card_eq_pow_finrank` together with MR-1.
   - For W ∈ Ω_Y, `[Y | W]` has the same range as `[Y | 0]`, so it has rank i, and `fourierCoeff_eq_of_same_range` gives F̂([Y | W]) = F̂([Y | 0]).
   - `(Y, W) ↦ [Y | W]` is injective, and every term is nonnegative.
   - Hence 2^{is} · post ≤ full.
5. **Matching the contract.** With full ≥ 0, `−is ≤ −i(s−1)` and `3·2^{i−n} ≥ 0`, this gives the contract's right-hand side exactly.
6. **What it uses and keeps.** None of `hEven`, ρ, `hc`, `hs`, `hHeight` or `hi` is used. All remain as binders, so the full original target and every guard are retained.

**Edge cases:** i > c (post is empty), d = 0, n = 0, s = 0 (Ω_Y = {0}), and i = 0 are all handled with no division. I agree the argument is sufficient. The three prior argument reports reached the same conclusion; their stated input gaps (Rank, coordinate equivalence, alignment audit) are closed above.

**Still open in this route:** the native translation; the fidelity check against manuscript Lemma 4.7; and the universal count, energy, gain and contract proofs.

## 6. Integration and custody

- **Same objects throughout.** The SourceSize, HC46 and Dyadic export bodies are byte-identical, and their object hashes are unchanged (for example Dyadic C02909B6…, AnalyticMoment B472BC2E…). So these checks carry forward as earlier verified:
  - the same `I`/copies/U/A/C/T/f, with `Tc` used in `hfail`, the PR premise and the moment;
  - `rows` independent of `m`;
  - `c+s = 2h ≤ 2J`, with `hdim`, `hD` and `hsmall` derived;
  - `original_HC46_exact` applied at `hEven := hsplit`;
  - a caller-chosen dyadic `k ≥ 4m`;
  - `hsel`, `hA`, `hrd`, `hfail` and `hSpectral` all retained;
  - no uniform/rank-one replacement of the append experiment and no narrowed source/star family.
- **Not yet consumed.** The new helpers feed no export, so `hSpectral` remains a premise everywhere.
- **Bookkeeping.**
  - Roots: 184 + 8 = 192 (the 8 are exactly the 8 new declarations).
  - Focused set: 16 + 8 = 24. Modules: 200 + 2 = 202. Sources: 325 + 2 = 327.
  - Nodes: 8072 → 8084 with all 8072 shared edges unchanged; external boundaries 2738 → 2740. This is plausible, but no per-node enumeration was supplied.
- **Typed custody.**
  - Source SHAs from the headers: RightOrbit 409FD652…, Covariance CF8990EA…. These equal both `source_sha256` and the alignment-audit SHAs.
  - Object SHAs: 79CC0A45… and EFF637A8…. These equal the values in the legacy `added_object_hashes`.
  - The two categories are never compared to each other, so H1 stays closed as a category error.
  - The Mathlib file SHAs appear only as headers; I cannot cross-check them against index members.

## 7. Findings

| ID | Sev. | Declaration | Disposition / action |
|---|---|---|---|
| RO-1 | Verified | `same_range_matrix_right_orbit` | None |
| RO-2 | Verified | `basis_invariant_eq_of_same_range` | None |
| FC-1…6 | Verified | `rightBasisEquiv`, `pairing_mul_right`, `character_mul_right`, `uniformMean_comp_equiv`, `fourierCoeff_mul_right_of_basis_invariant`, `fourierCoeff_eq_of_same_range` | None |
| MR-1 | Closed input gap | Mathlib `rank` / `toLin'` | None |
| CE-1 | Closed input gap; Low debt | append equivalence, `appendBinaryMatrix_range_eq_span` | Add a matrix-form range lemma |
| ALN-1 | Closed (review) | alignment audit | None |
| ALN-2 | Info | `BinaryMatrixFourier` body | Supply it for a fresh read |
| SP-1 | **Medium, open** (carried) | `Spectral47ExactContract` | Native inhabitant via §5, then a consuming export with `hSpectral` removed |
| FID-1 | Low/Medium, open (carried CB-2) | contract vs manuscript Lemma 4.7 | Fidelity audit. Guards are unused, and the 3·2^{i−n} term and the −1 are slack. |
| HY-1 | Low | RightOrbit header says "not native qualified" | Stale wording; fix in a new revision. The immutable input is not mutated. |
| N-4 | Low (carried) | stale "uncompiled" banners elsewhere | Historical bytes; hygiene |
| R14 | **HIGH, open (outside scope)** | encoded reduction/runtime | Bars overall GO |

## 8. Safe conditional claim

This rests on pinned kernel and library trust, the qualified receipts (192 standard profiles, seven exits of 0), the typed identities, and identity reuse. Under those, the earlier SourceSize/Dyadic material bounds stand unchanged, and in addition:

- equal-range binary matrices are related by a right multiplication by a paired-inverse matrix, with no rank hypothesis;
- every function invariant in the `basisInv` sense has Fourier coefficients that are constant on equal-range classes.

**Not claimed:**
- universal Spectral47, or its fidelity to Lemma 4.7;
- an HC46-based contract inhabitant beyond the existing one, a useful numeric NO bound, or `hfail`/`e`;
- a joint source/selector/star/robust8S witness or the pre-draw table;
- the physical sampler;
- encoded reduction, runtime or learning;
- exact upstream transports;
- warning-free status or fresh-checkout certification (inherited baseline warnings are preserved);
- novelty, citations, PDF or publication;
- priority or any unconditional theorem.

## Remaining to-do

1. **Native Spectral47:**
   - the product-mean lemma and the append coefficient identity;
   - the matrix-form range lemma (CE-1), giving `rank [Y | W] = rank Y` for W ∈ Ω_Y;
   - the rank-level Parseval identities;
   - `card Ω_Y = 2^{is}` and the injection inequality;
   - the rpow transfer;
   - an inhabitant of `∀ cutoff, Spectral47ExactContract cutoff` with every guard kept as a binder, transported through `spectral47_contract_iff`.
2. A new export consuming that inhabitant, which removes `hSpectral`; then re-run the exact trace and a fresh review.
3. Fidelity audit against manuscript Lemma 4.7.
4. Supply the `BinaryMatrixFourier` body for a fresh read (ALN-2).
5. Numeric NO: a certified scalar consumer and a useful `e`/`hfail` compared against the actual selection bound.
6. A joint source/selector/copies/U/A witness; source/star/robust8S; the pre-draw global table; the physical sampler.
7. R14: encoded reduction and runtime, plus learning.
8. Upstream post-audit, then the exact CMMSA bridges.
9. Hygiene: stale banners (HY-1, N-4), the legacy hash field, warning-debt disposition, and a fresh-checkout replay with hashes recomputed.
10. Release: manuscript fidelity, novelty and citations, PDF, final providers.
