# Full100 identity/body addendum: independent proof-adversarial review

The addendum closes all four gaps at the review and enumeration tier, with two residuals and one new item:

- **Residual 1:** the `BinaryMatrixFourier` source hash cannot be compared against the Full100 capture. The packet has no capture record for that file.
- **Residual 2:** the native inventory holds **331** `.olean` entries, not 327.
- **New item:** the native archive shows a 3 MB tracked diff in the `cslib` package.

The original conditional GO-WITH-NOTES and every broader HIGH and Medium finding stay as they were.

## Verdicts

| Scope | Verdict |
|---|---|
| **ALN-2 / NC100-7 / CX100-08**: the complete `BinaryMatrixFourier` body | **Body verified.** I read all of it and re-derived every definition and normalization (§2). **Its source identity is only partly bound** (§2.4). |
| **NC100-8**: the 661 native objects | **Closed at the inventory and terminal tier.** 661 entries = 331 `.olean` + 330 `.olean.hash`. A new residual: there are 331 `.olean` entries against 327 expected (§3). |
| **CX100-12**: +12 nodes and +2 boundaries | **Closed at the enumeration tier.** All 12 nodes are listed, and I decoded their type DAGs against the source statements. The 2 boundaries are named (§4). |
| **Three Mathlib sources in the 409-file index** | **Accepted at the supplied-record tier** (§5). |
| **Conditional material integration** | **GO-WITH-NOTES, unchanged.** No bytes change in this addendum. |
| **Unconditional material readiness, universal Spectral47, unconditional theorem, numeric NO, source/runtime witness** | **No.** Nothing here changes these. |
| **Overall GO** | **Not issued.** R14 (HIGH) and the other full-scope gates are still open. |
| **Manuscript fidelity, priority** | No verdict. |

**Method.** I used no tools, made no writes and ran no Lean, Lake or subagents. Every hash check is a string comparison of values in the packet; I recomputed none, including the type-DAG digests. Hash categories are kept apart: source, object, `.olean.hash` sidecar and type-DAG digest are never compared across categories.

## 1. Coverage

| Body or evidence | Status |
|---|---|
| `BinaryMatrixFourier.lean` (header SHA 810324DD…70D8) | **Read in full, every declaration** (listed in §2.1) |
| The 12 new native nodes (type DAG plus type, proof and union edges) | **Every node inspected.** I decoded each type DAG through its de Bruijn binders (§4). |
| The 2 new external boundary records | Inspected |
| Native inventory (661 entries), both archive member lists, trace terminal | Inspected. I enumerated the `.olean` paths by hand. |
| The three index member records | Inspected |
| **Not supplied, so not reviewed:** | |
| Mathlib `Data/Matrix/Diagonal.lean` (body of `transpose_one`) | Pinned trust only |
| Contents of `source-after.json`, `compiled-project-objects.json`, `core-source-hashes.json` | Not reproduced, which limits §2.4 and §3 |
| Contents of `cslib-tracked-diff.patch` (3,098,175 bytes) | Not reproduced (§6) |
| The 409-file index itself; the actual `.olean` binaries | Not supplied, as you stated |

**Skipped required fresh bodies: none.**

## 2. `BinaryMatrixFourier`: body read and normalization re-derived

### 2.1 Declarations

**Carrier and core definitions**
- **Carrier.** `BinaryMatrix n d := Matrix (Fin n) (Fin d) (ZMod 2)`, written G below.
- **`uniformMean f`** `= (Σ_M f M) / card G`. The mean is normalized.
- **`pairing Y M`** `= Σᵢ Σⱼ Y i j · M i j`, computed in ZMod 2. It is entrywise and puts Y first; it is not a matrix product.
- **`character Y M`** `= if pairing Y M = 0 then 1 else −1`, a real-valued ±1.

**Additivity**
- **`bitSign_add`.** Checked with `fin_cases` on all 4 cases, using `1+1=0` by `decide`.
- **`pairing_add_left` / `pairing_add_right`.** Pairing is additive in each argument.
- **`character_add_left` / `character_add_right`.** The character is multiplicative in each argument.

**Orthogonality**
- **`matrixUnit` and `pairing_matrixUnit`.** Pairing with the unit E_ij gives `Y i j`. The `single_apply` reduction is correct.
- **`character_sum_zero_of_ne`.**
  - Since Y ≠ 0, some entry Y_ij is nonzero, so χ_Y(E_ij) = −1.
  - The shift M ↦ M + E_ij is a bijection, so the sum S equals itself and also equals −S. Hence S = 0. This is sound.
- **`matrix_neg_self`, `matrix_add_self`.** These are the characteristic-2 identities.
- **`character_orthogonality`.**
  - It states mean(χ_Y χ_Z) = [Y = Z].
  - If Y = Z: χ_{Y+Y} = χ₀ = 1, so the mean is card/card = 1.
  - If Y ≠ Z: Y + Z ≠ 0, because Y + Z = 0 would force Y = −Z = Z.
  - Degenerate shapes (n·d = 0): G has one element, so the Y ≠ Z branch is vacuous.
- **`pairing_comm`, `character_comm`, `character_dual_orthogonality`.** Checked.

**Fourier coefficients, inversion and Parseval**
- **`fourierCoeff f Y`** `= uniformMean (f · χ_Y)`.
- **`fourier_inversion`.**
  - Σ_Y f̂(Y) χ_Y(M) = (1/|G|) Σ_N f(N) Σ_Y χ_Y(N) χ_Y(M) = (1/|G|) Σ_N f(N) · |G| · [N = M] = f(M).
  - `hcard ≠ 0` comes from `Fintype.card_pos`; G is nonempty because it contains 0.
- **`fourier_parseval`.** mean(f²) = (1/|G|) Σ_M Σ_Y f̂(Y) χ_Y(M) f(M) = Σ_Y f̂(Y)².

**Rank projection**
- **`rankProjection i f M`** `= Σ_{Y : Y.rank = i} f̂(Y) χ_Y(M)`.
- **`fourierCoeff_rankProjection`.** The coefficient at Z is Σ_{Y ∈ s} f̂(Y)[Y = Z] = [Z.rank = i] f̂(Z). Re-derived.
- **`rankProjection_energy_le`.** This is Bessel's inequality, via Parseval on both sides.
- **`rank_eq_zero_iff`, `rankProjection_zero`.** Checked.

**Remaining helpers**
- `lpMoment`, `lpNorm` (with exponent `1/(p:ℝ)`; p = 0 gives exponent 0, which is harmless because every use has p ≥ 4).
- `AffineRestriction` and its `fibre`, `budget`, `density`.
- `Pseudorandom` and `PseudorandomExact`.
- `wholeRestriction` and `exactWholeRestriction` (fibre = univ; budget 0 and r).
- The `boolean_mean_le_*` lemmas, `uniformMean_const` and `uniformMean_indicator_nonneg`.
- The rank-zero results `rankZero_lpNorm_le`, `binary_hc_rankZero` and `binary_hc_rankZero_exact`. Here 2^(500·0²·p) = 1, and δ ≤ δ^(1−2/p) via `self_le_rpow_of_le_one` for δ ∈ [0,1] with exponent ≤ 1. Sound.
- `binary_hc_rankLevel_L2_exact`: `lpMoment 2` is the mean of squares by `sq_abs`, followed by Bessel and indicator² = indicator. Sound for every i, including i above the matrix dimensions.

The header says "analytic hypercontractive inequality not asserted". That is accurate: only the rank-0 slice and the L² rank-level bound are proved.

### 2.2 Normalization summary

| Object | Normalization |
|---|---|
| `uniformMean` | Divided by \|G\| |
| `fourierCoeff` | Normalized: (1/\|G\|) Σ f·χ |
| Inversion | Plain sum over Y, with no factor |
| Parseval | Normalized mean of f² = plain sum of f̂² |
| Characters | ±1 in ℝ; the character of the zero frequency is constantly 1 (`character_zero_left`) |

**Consistency with the Spectral47 injection route.**
- The coefficient identity of `A_s g` at Y is (1/2^{nc}) Σ_M (1/2^{ns}) Σ_B g([M|B]) χ_Y(M).
- Since χ_{[Y|0]}([M|B]) = χ_Y(M), this equals ĝ([Y|0]) exactly. It needs only 2^{nc} · 2^{ns} = |Mat(n,c+s)| (CN-1).
- Both energies are plain sums of normalized coefficients over their own carriers, so 2^{is} · post ≤ full has no normalization mismatch.
- **Translation note:** if the contract is phrased with `lpMoment 2` or `lpNorm`, you need the `sq_abs` rewrite (as used in `binary_hc_rankLevel_L2_exact`) plus the rpow step.

### 2.3 Consistency with compiled call sites

These checks corroborate the body; they do not establish its identity.
- The edges of `uniformMean_comp_equiv` include `Finset.sum`, `Fintype.card`, `HDiv.hDiv` and `Nat.cast`, which fits sum/card.
- The edges of `pairing_mul_right` include `Finset.sum_comm`, `sum_mul` and `mul_sum`, which fits the double sum.
- The edges of `character_mul_right` include `ite`, `Real.instNeg`, `Real.instOne` and `ZMod.decidableEq`, which fits if/±1.
- The type DAGs apply `character`, `pairing` and `fourierCoeff` with argument order `n d Y M` and `n d F Y`, which fits the source binders.
- `uniformMean._proof_1` appears as an auxiliary of this unchanged module. It is consistent with the `ZMod.fintype` and `NeZero` instance edges, and it is not a new node.

### 2.4 Source identity: partly bound

- The file declares SHA **810324DD…70D8**.
- **No Full100 capture value for `lean/PvNP/RealizableHardness/BinaryMatrixFourier.lean` appears in this packet.**
  - The three original reports never quote it.
  - `source-after.json` is listed only by size (45822 bytes, the same size as `source-before.json`).
- I therefore **cannot** string-compare it against the unchanged Full100 capture.
- The inventory values `A8721515…E240` (`.olean`) and `4F1D2794…8CB4` (`.hash`) are object-category values. I deliberately did not compare them with the source SHA.
- **Disposition:** the semantics are closed; binding the identity to the capture remains a Low residual (ID-F1).

## 3. NC100-8: the 661 objects

**What reconciles**
- **Hand enumeration.** I counted the inventory one module at a time. It has **331 `.olean` paths** (all under `PvNP/RealizableHardness`) and **330 `.olean.hash` entries**, for a total of 661.
- **The one unpaired entry.** `ActualBinaryMatrixHC46A7TransferOwnedChecks.olean` (32C9DED3…5525) has no `.hash` sidecar. That is why the total is odd.
- **I could not machine-check this count.** If it is off by one or two, the "331 vs 327" observation below shifts, but the total of 661 still has to be odd.
- **Terminal agreement.** The terminal reports `compiled_objects_preserved: 661`, `project_sources_preserved: 327`, `project_object_closure: 327`, probe exit 0 and `failure: null`.
- **Archive binding.** The terminal's `native_archive_sha256` 66BFF34B…8475 equals the remote, short and repository SHA of the native custody. The run id `c0fd3e11` matches the paths.
- **Typed object spot checks.** RightOrbit is 79CC0A45…F06972 and RightFourierCovariance is EFF637A8…B1030. Both match the truncated original values. Dyadic (C02909B6…) and SourceSize AnalyticMoment (B472BC2E…) are unchanged.
- **Disposition:** the count is reconciled at the inventory and terminal tier, as you stated. This is not binary archiving and not a replay.

**New residual (NA-1, Low)**
- The inventory has 331 `.olean` entries. The record field `actual_project_olean_count` says 327, and the closure is 327.
- So the inventory is a superset with **4 unidentified extra `.olean` entries**. Plausibly these are `*Checks` or `OwnedChecks` modules outside the root closure, but the packet does not say.
- The expected list of 327 lives in `compiled-project-objects.json` or `source-after.json`, which are not reproduced. So the claim that every one of the 327 is present is **asserted, not independently checked**.
- The missing sidecar for `A7TransferOwnedChecks` needs a disposition.

**Also noted.** The terminal records `consumption_coverage_complete: false`, `reviewed: false` and `accepted: false`. I read the terminal only as a preservation binding, not as a coverage certificate.

## 4. CX100-12: the 12 nodes and 2 boundaries, enumerated

| # | Node | Kind | Decoded type (from the DAG binders) | Notes on edges |
|---|---|---|---|---|
| 1 | `LinearMap.toMatrix'_id` (Mathlib, ToLin) | external thm | `∀ {R}[CommSemiring R]{n}[DecidableEq n][Fintype n], toMatrix' LinearMap.id = 1` | Proof uses `Matrix.ext`, `toMatrix'_apply`, `one_apply`. It is in ToLin.lean, which was read in full in Full100. |
| 2 | `Matrix.transpose_one` (Mathlib, Data.Matrix.Diagonal) | external thm | `∀ {n α}[DecidableEq n][Zero α][One α], (1)ᵀ = 1` | Union = type + `diagonal_transpose`. **The source is not supplied, so this is pinned trust.** |
| 3 | `character_mul_right` | project thm | `∀{n d}(Y M : BM n d)(U : BM d d), χ(Y·U) M = χ Y (M·Uᵀ)` | Uses `pairing_mul_right`. The transpose sits on the data. |
| 4 | `pairing_mul_right` | project thm | Same shape in ZMod 2 | Uses `ring`/`Finset` sum lemmas |
| 5 | `rightBasisEquiv` | definition | `∀{n d}(U V : BM d d), U·V=1 → V·U=1 → BM n d ≃ BM n d` | Uses `Equiv.mk`, `_proof_1`, `_proof_2` |
| 6 | `rightBasisEquiv._proof_1` | auxiliary | `… (hUV) (M), M·U·V = M` | Uses `mul_assoc`, `mul_one`. This is `left_inv`. |
| 7 | `rightBasisEquiv._proof_2` | auxiliary | `… (hVU) (M), M·V·U = M` | This is `right_inv` |
| 8 | `uniformMean_comp_equiv` | project thm | `∀ e H, uniformMean (H ∘ e) = uniformMean H` | Uses `Equiv.sum_comp` |
| 9 | `fourierCoeff_mul_right_of_basis_invariant` | project thm | `∀ F (hInv: ∀ M U V, UV=1→VU=1→F(MU)=F M) Y U V hUV hVU, F̂(Y·U) = F̂(Y)` | Uses `transpose_mul`, `transpose_one`, `rightBasisEquiv`, `uniformMean_comp_equiv`, `character_mul_right` |
| 10 | `fourierCoeff_eq_of_same_range` | project thm | `∀ F hInv (Y Z : BM n d), range(toLin' Y)=range(toLin' Z) → F̂ Y = F̂ Z` | Uses `basis_invariant_eq_of_same_range` and node 9. The submodule is in `Fin n → ZMod 2`. |
| 11 | `basis_invariant_eq_of_same_range` | project thm | `∀ {A : Type u_1} F hInv M N, range eq → F M = F N` | Uses `same_range_matrix_right_orbit` |
| 12 | `same_range_matrix_right_orbit` | project thm | `∀ M N, range(toLin' M)=range(toLin' N) → ∃ U V : BM d d, U·V=1 ∧ V·U=1 ∧ N·U=M` | Uses `same_range_right_orbit`, `toMatrix'_comp`, `toMatrix'_toLin'`, `toMatrix'_id`, `LinearEquiv.symm` |

**Results**
- **Statements.** Every decoded binder order, matrix dimension (U and V are d×d; contraction uses `Fin.fintype d`) and orientation matches the source statements verified in the original reports. The `hInv` binder order `(M U V) UV VU` matches `_basisInv`.
- **Edge hygiene.** No `sorryAx` appears in any edge set. Project edges reach only `BinaryMatrixFourier`, `SameRangeOrbit` and the two new modules.
- **Breakdown of the 12.** The 12 nodes are the 8 declared roots, 2 auxiliary proof fields and 2 external nodes. The original inference ("8 plus auxiliaries") was partly right; this enumeration corrects it.
- **Boundaries.** 2738 → 2740 is exactly `toMatrix'_id` and `transpose_one`. Both records say "disposition pending".
  - `toMatrix'_id` is covered by the Full100 full read of ToLin.lean.
  - `transpose_one` is not covered. It is a residual (BD-1, Low, pinned trust).
- **Not recomputed.** I did not recompute the 12 `exact_type_dag_sha256` values or the claim that the 8072 shared edges are unchanged.

## 5. The three sources' membership in the 409-file index

| File | Record SHA | Original header prefix | Bytes | Revision |
|---|---|---|---|---|
| `Mathlib/LinearAlgebra/Matrix/Rank.lean` | 4CE45784…E262 | 4CE45784 ✓ | 29408 | e06eff5f… |
| `Mathlib/LinearAlgebra/Matrix/ToLin.lean` | 9AEFBF5B…B1CD | 9AEFBF5B ✓ | 52679 | e06eff5f… |
| `Mathlib/FieldTheory/Finiteness.lean` | 05316F2A…AC00 | 05316F2A ✓ | 4050 | e06eff5f… |

- All three records have `complete_source: true`, and all paths are under `.lake/packages/mathlib`.
- The index SHA is 86C36CF4…EF18.
- **Limits:**
  - The original reports quoted only 8-character prefixes, so my comparison is limited to those prefixes.
  - The index itself is not supplied. Membership rests on the supplied records and on your statement that they were root-verified; I did not root-verify them myself.
- This closes the original note that the reports could not cross-check against index members. It closes it at the record tier.

## 6. New observation from the archive member list

**CS-1 (severity undetermined).**
- `cslib-tracked-diff.patch` is **3,098,175 bytes**. Every other tracked-diff patch is 0 bytes.
- So `cslib` is not at a clean pinned revision in the native capture.
- If any `cslib` file is in the 327 or 409 closure, pinned-trust is weakened for it, and the severity would be at least Medium. If none is, this is hygiene only (Low).
- The packet does not say which applies.

## 7. Dispositions of the original findings

| Original ID | Original severity | Addendum disposition |
|---|---|---|
| ALN-2 (proof-adversarial) | Info | **Closed (body re-derived)**, with residual ID-F1: the source SHA is not bound to the capture |
| NC100-7 (non-claims) | Low | **Closed for semantics**, with residual ID-F1 |
| CX100-08 (complexity) | Low | **Closed for the body re-check.** Line numbers are still unverified. The frame-pushforward obligation is still removable under the injection route. |
| NC100-8 | Info | **Closed at the inventory and terminal tier** (661 = 331 + 330), with residual NA-1 |
| CX100-12 | Low | **Closed at the enumeration and type-decode tier**, with residuals BD-1 and digest recomputation |
| Three-source index membership note | — | **Closed at the record tier** |
| New | — | NA-1 (Low), BD-1 (Low), ID-F1 (Low), CS-1 (severity undetermined) |
| SP-1 / CX100-10 / NC100-5 (Spectral47 inhabitant) | Medium | **Unchanged, open** |
| FID-1 / CX100-11 / NC100-6 | Low/Medium | **Unchanged, open.** One note for the audit: by zero-padding, `PseudorandomExact r` is equivalent to `Pseudorandom r`, because nominal budget counts dependent and zero equations. |
| CE-1, HY-1/CX100-09/NC100-4, N-4, legacy field, warning debt | Low | Unchanged |
| Numeric NO, joint witnesses, source/star/robust8S, pre-draw table, sampler | Medium | Unchanged, open |
| **R14** | **HIGH** | **Unchanged, open. Bars overall GO.** |

## 8. Readiness

- **Conditional integration:** GO-WITH-NOTES, unchanged. These rest on pinned kernel and library trust, the qualified receipts, the typed identities and identity reuse:
  - the SourceSize and Dyadic bounds, with Spectral47 kept as a premise;
  - the orbit lemma;
  - Fourier constancy on same-range classes.

  The `BinaryMatrixFourier` definitions those results depend on are now reviewed directly.
- **Overall readiness:** not issued. The following still do not follow:
  - universal Spectral47, or any unconditional theorem;
  - a numeric NO bound;
  - source or runtime witnesses;
  - fresh-checkout replay;
  - a binary archive of compiled objects;
  - manuscript fidelity, or overall GO.

## Remaining to-do

1. **ID-F1:** produce the Full100 `source-after.json` record for `BinaryMatrixFourier.lean` and string-compare it with 810324DD…70D8.
2. **NA-1:** list the 327 expected `.olean` paths (from `compiled-project-objects.json`), name the 4 extra `.olean` entries, and explain why `A7TransferOwnedChecks` has no `.hash` sidecar.
3. **CS-1:** determine whether any `cslib` file is in the 327 or 409 closure. If so, review the 3 MB diff or re-pin the package.
4. **BD-1:** review `Mathlib/Data/Matrix/Diagonal.lean` for `transpose_one`, or record it explicitly as pinned trust.
5. Recompute the 12 type-DAG digests and the 8072 unchanged shared edges during replay.
6. **Native Spectral47** via the injection route:
   - the product-mean lemma;
   - the append coefficient identity;
   - the matrix-form range lemma (CE-1);
   - the rank-level Parseval energies (using `fourier_parseval` and `fourierCoeff_rankProjection` as reviewed here);
   - |Ω_Y| = 2^{is} and the injection inequality;
   - the `sq_abs` and rpow transfer;
   - `∀ cutoff, Spectral47ExactContract cutoff` with every guard kept, transferred through `spectral47_contract_iff`.
7. A consuming export without `hSpectral`, followed by an exact trace and a fresh review.
8. A fidelity audit against Lemma 4.7, including the nominal-budget and zero-padding semantics of `PseudorandomExact`.
9. Numeric NO: `hfail` at a useful `e`, `base`/`cutoff`, and an effective L₀.
10. Joint witnesses for source, selector, copies, U and A; source/star/robust8S; the pre-draw table; the physical sampler.
11. **R14:** encoded reduction and runtime; learning.
12. Upstream post-audit, then the CMMSA bridges.
13. A fresh-checkout replay with every hash recomputed, plus a binary archive of compiled objects if required.
14. Hygiene: stale headers, the legacy field, the m-coupled roots, warning and linter debt.
15. Release: manuscript fidelity, novelty and citations, PDF, and the final providers.
