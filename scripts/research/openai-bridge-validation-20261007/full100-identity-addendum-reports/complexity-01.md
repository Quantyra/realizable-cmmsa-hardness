# Full100 identity and body addendum: complexity review

**Scope.** This addendum closes four evidence gaps from the original Full100 integration reports:

- **ALN-2 / NC100-7 / CX100-08:** the `BinaryMatrixFourier` body.
- **NC100-8:** the 661 native objects.
- **CX100-12:** the +12 trace nodes and +2 external boundaries.
- **Index membership** of the three supplied Mathlib sources.

The three original reports stand unchanged. Their conditional GO-WITH-NOTES verdict and every broader HIGH and Medium finding carry forward.

**Method.** I used no tools, made no writes, and ran no Lean, Lake or subagents. Every hash comparison below is a string comparison of values in the packet; I recomputed nothing. I counted the inventory by hand.

## Verdicts

| Scope | Verdict |
|---|---|
| `BinaryMatrixFourier` body | **Read in full and re-derived.** No soundness or normalization defect. Its source identity is only header-tier (§1.4). |
| NC100-8 (661 objects) | **Reconciled at the inventory and terminal tier, with two new Low notes** (§2). |
| CX100-12 (+12 nodes / +2 boundaries) | **Closed by enumeration.** All 12 node types decoded from their type DAGs (§3). |
| Three Mathlib sources in the 409-file index | **Closed at the tier of the supplied member records** (§4). |
| Conditional material integration | **GO-WITH-NOTES, conditional. Unchanged.** |
| Overall GO | **Not issued.** R14 is still an open HIGH, and the Spectral47 inhabitant (SP-1 / CX100-10 / NC100-5) is still open. |

## 1. `BinaryMatrixFourier` body (810324DD…70D8)

### 1.1 Definitions, re-derived

| Object | Definition | Normalization |
|---|---|---|
| `BinaryMatrix n d` | An abbreviation for `Matrix (Fin n) (Fin d) (ZMod 2)` | The carrier always has at least one element (exactly 1 when n = 0 or d = 0), so the card is never 0. |
| `uniformMean f` | `(Σ_M f M) / card` | A probability expectation, with card = 2^{nd} |
| `pairing Y M` | `Σ_i Σ_j Y_ij · M_ij` in ZMod 2 | The trace pairing tr(YᵀM). It is bilinear and symmetric. |
| `character Y M` | `if pairing Y M = 0 then 1 else −1` | Equals (−1)^{⟨Y,M⟩} |
| `fourierCoeff f Y` | `uniformMean (f · χ_Y)` | Expectation-normalized: f̂(Y) = 2^{−nd} Σ_M f(M) χ_Y(M) |
| `rankProjection i f M` | `Σ_{Y.rank = i} f̂(Y) · χ_Y(M)` | No extra factor. `Matrix.rank` comes from the root-verified `Rank.lean`, so rank = finrank (range (toLin' Y)) (MR-1). |

### 1.2 Theorems, each re-derived

- **`bitSign_add`.** Checked case by case (`fin_cases`), using 1 + 1 = 0.
- **Pairing linearity and character multiplicativity.** `pairing_add_left/right` and `character_add_left/right` hold by linearity and `bitSign_add`.
- **`pairing_matrixUnit` gives `Y i j`.** It uses the `Matrix.single_apply` orientation `i = x ∧ j = z`, which is correct.
- **`character_sum_zero_of_ne`.**
  - Shifting by `E = matrixUnit i j` with Y_ij ≠ 0 is a bijection, so S = Σ_M χ_Y(M + E) = −S, hence S = 0.
  - When n = 0 or d = 0, the premise Y ≠ 0 is vacuous.
- **`character_orthogonality`.** E[χ_Y χ_Z] = [Y = Z]. It uses Y + Y = 0 (characteristic 2) and Y + Z = 0 ⇒ Y = −Z = Z. `character_dual_orthogonality` follows by symmetry.
- **`fourier_inversion`.** f(M) = Σ_Y f̂(Y) χ_Y(M), with no factor. It uses Σ_Y χ_Y(N) χ_Y(M) = card · [N = M].
- **`fourier_parseval`.** E[f²] = Σ_Y f̂(Y)², with the expectation on the data side and counting measure on frequencies.
- **`fourierCoeff_rankProjection`.** (P_i f)^(Z) = [rank Z = i] · f̂(Z).
- **`rankProjection_energy_le`.** This is Bessel's inequality.
- **`rank_eq_zero_iff` and `rankProjection_zero`.** Both correct; P₀ f is the constant `uniformMean f`.

### 1.3 Normalization consequence for the Spectral47 route

Both `uniformMean` and `fourierCoeff` are normalized as expectations on their own carriers. So, with the product-mean reindex, (A_s g)^(Y) = ĝ([Y | 0]) carries no factor of 2^{ns}.

Post-energy and full-energy are both Parseval sums over their own frequency sets. The gain 2^{is} is therefore a pure count of |Ω_Y|, with no hidden normalization factor. This confirms the original §5 derivations against the actual body.

### 1.4 Cross-checks against kernel use

The union edges of the new nodes match the body:

- `uniformMean_comp_equiv` reaches `Finset.sum`, `HDiv`, `Fintype.card`, `Nat.cast` and `uniformMean._proof_1`, which is the sum-over-card shape.
- `character_mul_right` reaches `ite`, `Neg.neg`, `Real.instOne` and `ZMod.decidableEq`.
- `pairing_mul_right` reaches `Finset.sum_comm`, `Finset.mul_sum` and `Finset.sum_mul`.
- `fourierCoeff_mul_right_of_basis_invariant` reaches `uniformMean`, `character` and `Real.instMul`.

The `Fintype` instance chain is the same at every use (`Matrix.instFintypeOfDecidableEq`, `ZMod.fintype`, `Nat.instNeZeroSucc`). So every card normalization refers to the same object.

### 1.5 Typed identity

- **Object.** `BinaryMatrixFourier.olean` is A87215154DE7…E240, with `.hash` 4F1D2794…8CB4. Both appear in the object-after inventory.
- **Source.** 810324DD…70D8 comes only from the file header. I cannot string-match it against the unchanged Full100 capture: `source-after.json` is listed as an archive member but its contents are not expanded, and the alignment audit's hash for this path is not quoted in the packet.
- **Category separation.** The source and object categories were never compared with each other, and no equality between them is claimed.
- **Residual (Low):** the source identity is header-tier only.

### 1.6 Rest of the file

I also read the rest of the file: `lpMoment`, `lpNorm`, `AffineRestriction`, `Pseudorandom` and `PseudorandomExact`, the whole-space restrictions, and the rank-zero and L² theorems. They are sound. Two notes:

- **Nominal budget.** The budget counts zero and dependent equations, so `PseudorandomExact r` directly gives a whole-space bound. The docstring states this, and Spectral47 does not depend on it. It belongs to the existing manuscript-fidelity item, not to this addendum.
- **Rank-zero constant.** In the rank-zero theorems, 2^{500·0²·p} = 1.

## 2. NC100-8: the 661 native objects

- **Custody binding.** The terminal's `native_archive_sha256` (66BFF34B…8475) equals the native custody's remote, short and repository SHA. The run identifier equals the native run directory name. The timestamps are in order: native 09:25:34, trace directory 10:39:39, terminal 10:40:11.
- **Counts.** The terminal binds 661 objects, 327 sources and 327 for the object closure. Probe exit is 0, with no failure.
- **Inventory decomposition (my hand count).** All entries are under `PvNP/RealizableHardness/`:
  - **331 `.olean` + 330 `.olean.hash` = 661.** Those two numbers add up exactly to the stated total, which supports the count.
  - **New note NC-A (Low):** there are 331 `.olean` files against 327 project sources, so **4 `.olean` objects lie outside the 327-source closure.** They cannot be identified, because the 327-path source list is not expanded. Superset membership is consistent with `all_project_oleans_present: true`.
  - **New note NC-B (Low):** `ActualBinaryMatrixHC46A7TransferOwnedChecks.olean` (32C9DED3…5525) has **no `.hash` sidecar**. It is the only one I found.
- **Membership spot checks.** These modules are present: `BinaryMatrixFourier`, `RightOrbit`, `RightFourierCovariance`, `SameRangeOrbit`, `SourceSizeContractBridge`, `MatrixLiftAffineTarget`, `FiniteMomentLpBounds`, `AppendOperator`, and both `Dyadic` and `SourceSize` `AnalyticMoment`. I cannot check all 327 for the reason above.
- **Object hashes against the original reports.**
  - RightOrbit 79CC0A45…F06972: matches.
  - Dyadic C02909B6…: matches.
  - SourceSize AnalyticMoment B472BC2E…: matches.
  - RightFourierCovariance EFF637A8…DC1B030 matches the prefix and the non-claims report's suffix "…B030".
  - **Erratum in the preserved CX100 report (not mutated):** its abbreviation "EFF637A8…B1030" has a transposed suffix. The actual tail is "…1B030".
- **Terminal flags.** The terminal itself records `consumption_coverage_complete: false`, `reviewed: false`, `accepted: false` and `local_compilation: false`. It binds and preserves objects; it does not certify consumption.
- **Unexplained relation.** The earlier figure `cache_objects_unchanged: 566` is not explained relative to 661.
- **No binary archive.** No archive member contains the `.olean` binaries, which agrees with `compiled_object_binary_archive_claimed: false`.

## 3. CX100-12: the +12 nodes and +2 boundaries, enumerated

I decoded each type from its DAG by tracking binder indices. I did not recompute the DAG digests.

| # | Node | Kind | Decoded type | Matches report? |
|---|---|---|---|---|
| 1 | `same_range_matrix_right_orbit` | thm | ∀{n d} M N, range toLin' M = range toLin' N → ∃ U V : BM d d, U·V = 1 ∧ V·U = 1 ∧ N·U = M | Yes |
| 2 | `basis_invariant_eq_of_same_range` | thm | ∀{n d}{A : Type u₁} F hInv M N h, F M = F N. `hInv` covers every M, U, V with both inverse laws. | Yes |
| 3 | `rightBasisEquiv` | def | (U V : BM d d) → U·V = 1 → V·U = 1 → BM n d ≃ BM n d | Yes |
| 4 | `rightBasisEquiv._proof_1` | thm | hUV ⊢ ∀ M, (M·U)·V = M (`left_inv`) | Auxiliary |
| 5 | `rightBasisEquiv._proof_2` | thm | hVU ⊢ ∀ M, (M·V)·U = M (`right_inv`) | Auxiliary |
| 6 | `pairing_mul_right` | thm | pairing(Y·U, M) = pairing(Y, M·Uᵀ) | Yes; the transpose is on the data |
| 7 | `character_mul_right` | thm | χ(Y·U, M) = χ(Y, M·Uᵀ) | Yes |
| 8 | `uniformMean_comp_equiv` | thm | uniformMean (H ∘ e) = uniformMean H | Yes |
| 9 | `fourierCoeff_mul_right_of_basis_invariant` | thm | F̂(Y·U) = F̂(Y), under hInv, hUV and hVU | Yes |
| 10 | `fourierCoeff_eq_of_same_range` | thm | F̂ Y = F̂ Z when range toLin' Y = range toLin' Z (toLin' over Fin n × Fin d) | Yes |
| 11 | `LinearMap.toMatrix'_id` (external, `Matrix.ToLin`) | thm | toMatrix' id = 1 | Used by #1 |
| 12 | `Matrix.transpose_one` (external, `Matrix.Diagonal`) | thm | (1 : Matrix n n α)ᵀ = 1 | Used by #9 for 1ᵀ |

- **Breakdown.** 12 = 8 root declarations + 2 auxiliary proofs + 2 externals, so 8072 + 12 = 8084. The **+2 boundaries are exactly nodes 11 and 12**, so 2738 + 2 = 2740. This confirms the original CX100 inference by enumeration.
- **Union-edge spot checks.**
  - For `transpose_one`, 9 type edges plus `diagonal_transpose` give the 10 union edges.
  - For `character_mul_right` and `uniformMean_comp_equiv`, every type edge is contained in the proof edges, and the union equals the proof list.
  - In the sampled DAGs, child indices precede their parents, and the root is the outermost binder.
- **Boundary dispositions.**
  - **`toMatrix'_id`.** Its source is in `ToLin.lean` (9AEFBF5B…), which was read in full in Full100, and its proof edges (`Matrix.ext`, `toMatrix'_apply`, `Pi.single_apply`, `one_apply`) are standard. **Closed at the source-read tier.**
  - **`transpose_one`.** `Data/Matrix/Diagonal.lean` was not supplied, and its index record is not shown. **Pending, Low.** The statement is trivial, and its single proof edge is `diagonal_transpose`.
- **Not verifiable here.** I cannot check that every other constant these nodes reference already lies in the prior 8072 set; that rests on the receipt.

## 4. The three Mathlib sources in the index

| Path | SHA | Bytes | Revision | Matches the original reports' header? |
|---|---|---|---|---|
| `Mathlib/LinearAlgebra/Matrix/Rank.lean` | 4CE45784…E262 | 29408 | e06eff5f… | Yes |
| `Mathlib/LinearAlgebra/Matrix/ToLin.lean` | 9AEFBF5B…B1CD | 52679 | e06eff5f… | Yes |
| `Mathlib/FieldTheory/Finiteness.lean` | 05316F2A…AC00 | 4050 | e06eff5f… | Yes |

All three records state `complete_source: true`, and all three share one revision. The index SHA is 86C36CF4…EF18. I accept its root verification as supplied, but I cannot inspect the 409-member body itself.

## 5. Disposition of each original finding

| Finding | Disposition |
|---|---|
| ALN-2 / NC100-7 / CX100-08 (Fourier body) | **Closed for the body:** read in full, re-derived, and consistent with kernel use. **Low residual:** source identity is header-tier only (§1.5). The audit's line numbers stay unverified, and the CX100-08 note about updating the obligation list still stands. |
| NC100-8 (661 objects) | **Reconciled:** 331 + 330, bound by the terminal to the native archive SHA. **New Low notes:** NC-A (4 surplus `.olean` files) and NC-B (one missing `.hash`). |
| CX100-12 (+12 / +2) | **Closed by enumeration.** Digests not recomputed. |
| Index membership of the three Mathlib sources | **Closed at the record tier.** |
| Boundary `toMatrix'_id` | **Closed at the source-read tier.** |
| Boundary `transpose_one` | **Pending, Low.** |
| Erratum in the CX100 report | RightFourierCovariance object suffix should read "…1B030". Recorded here only; the preserved report is not changed. |
| Everything else (SP-1 / CX100-10 / NC100-5, FID-1 / CX100-11 / NC100-6, CE-1, HY-1 / CX100-09 / NC100-4, N-4, R14 and the carried Medium items) | **Unchanged and carried forward.** |

## 6. What I inspected and what I skipped

- **Inspected:**
  - the whole Fourier body;
  - all 12 node records (types decoded, edge lists read);
  - both boundary records;
  - both archive member lists;
  - the full object inventory (counted by hand);
  - the terminal record;
  - the three index records.
- **Skipped or not available:**
  - recomputing the DAG digests and any hashes;
  - the contents of `source-after.json`, `compiled-project-objects.json` and `probe.stdout`;
  - the 409-index body;
  - `Diagonal.lean`;
  - the old 8072-node set (to check edge closure);
  - the other roughly 278 project bodies (identity reuse only).

## 7. Readiness

- **Conditional integration:** GO-WITH-NOTES, conditional, unchanged. These closures strengthen the evidence but change no verdict.
- **Overall:** **not GO.**
- **Not established:** a universal Spectral47 inhabitant, any unconditional theorem, a numeric NO bound, source or runtime witnesses, fresh-checkout replay, a binary archive of the compiled objects, or manuscript fidelity.

## Remaining to-do

1. **Native Spectral47 via the injection route.** Prove the product-mean reindex, the append coefficient identity, the matrix-form range lemma, |Ω_Y| = 2^{is}, injectivity, the two Parseval energies, the gain bound and the rpow transfer. Then build `∀ cutoff, Spectral47ExactContract cutoff` with every guard kept, and transfer it through `spectral47_contract_iff`. Follow with a consuming export without `hSpectral`, a fresh review and an exact trace.
2. **Bind the source identity of `BinaryMatrixFourier`.** Expose the `source-after.json` entry or the audit hash for this path, and string-match it to 810324DD…70D8. Verify the audit's line numbers. Update the obligation list (CX100-08).
3. **Identify the 4 surplus `.olean` objects (NC-A)** against the 327-source list, explain the missing `.hash` for `A7TransferOwnedChecks` (NC-B), and reconcile the 566 cache-unchanged figure with 661.
4. **Review the `Matrix.transpose_one` boundary.** Supply `Data/Matrix/Diagonal.lean` and its index record.
5. **Check edge closure.** Show that every constant referenced by the 12 new nodes lies in the prior 8072 set, and recompute the 12 DAG digests during replay.
6. **Do the fidelity audit** against manuscript Lemma 4.7, including the nominal-budget modeling note.
7. **Numeric NO.** Certify the scalar consumer and a useful `e`/`hfail`.
8. **Joint witnesses.** Source, selector, copies, U and A; source/star/robust8S; the pre-draw table; the physical sampler.
9. **R14 (HIGH).** Encoded reduction and runtime, plus learning.
10. **Upstream.** Post-audit, then the CMMSA bridges.
11. **Hygiene.**
    - Do a fresh-checkout replay with every hash recomputed, and decide whether a binary archive of the compiled objects is needed.
    - Fix the stale banners (HY-1 / CX100-09 / NC100-4, N-4).
    - Retire the legacy object field and supersede the `m`-coupled roots.
    - Dispose of the warning debt.
    - Record the "…1B030" erratum in the next report revision.
12. **Release.** Manuscript fidelity, novelty and citations, BibTeX and PDF QA, and the final full-scope providers.
