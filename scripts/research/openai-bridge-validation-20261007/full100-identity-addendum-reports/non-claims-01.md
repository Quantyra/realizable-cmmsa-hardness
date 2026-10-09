# Full100 identity and body addendum: non-claims review

The three preserved Full100 reports are unchanged. This addendum only closes the specific evidence gaps you listed and does not change any original verdict.

**How I reviewed.** I used no tools, wrote nothing, and ran no Lean, Lake or subagents. I recomputed no hashes or type-DAG digests. Every hash comparison below is a string comparison between values in the packet. Inventory counts are my manual tallies of the JSON you supplied.

## Verdicts

| Scope | Verdict |
|---|---|
| `BinaryMatrixFourier` body (ALN-2 / NC100-7 / CX100-08) | **Closed for the body review.** I read it completely and re-derived every requested definition and its normalization. I found no defect. **Its source identity is not bound:** the packet has no Full100 capture record for this path to compare against (ADD-2). |
| 661 native objects (NC100-8) | **Reconciled at the inventory/terminal tier.** 661 is the number of inventory entries, not twice 327. There is a new Low residual (ADD-1). |
| +12 nodes / +2 boundaries (CX100-12) | **Closed.** I inspected all 12 nodes from their type DAGs and edge lists. I did not recompute the digests. Of the two boundaries, `toMatrix'_id` is reviewed and `transpose_one` is pinned trust only. |
| The three Mathlib sources in the 409-file index | **Closed at the record tier.** |
| Conditional material integration | **GO-WITH-NOTES, conditional. Unchanged and not upgraded.** |
| Unconditional material readiness | **No.** |
| Overall GO | **Not issued.** R14 is still an open HIGH. |

## 1. Coverage

| Body set | Status |
|---|---|
| `lean/PvNP/RealizableHardness/BinaryMatrixFourier.lean` (source 810324DD…70D8) | **Read line by line, every declaration.** |
| The 12 new trace nodes | Type DAGs decoded by hand to recover each exact statement. Proof, type and union edges checked for consistency. |
| Native archive (81 members) and trace archive (10 members) | Names and sizes inspected. Contents not supplied. |
| Object-after inventory | All entries tallied by hand. |
| Mathlib `Data/Matrix/Diagonal.lean` (holds the `Matrix.transpose_one` boundary) | **Not supplied, not read.** Pinned trust only. |
| The other 277 unsupplied project bodies | Identity reuse only, as before. |
| Patch contents, stage stdout/stderr, the 79 MB `probe.stdout`, `source-after.json`, the full 409-entry index | **Not supplied, not inspected.** |

**Skipped required fresh bodies: none.** The one body this addendum required, `BinaryMatrixFourier`, was read in full.

## 2. The `BinaryMatrixFourier` body, re-derived

Let N = |Mat(n,d)| = 2^{nd}. N is at least 1 even when n = 0 or d = 0, and the body discharges `hcard` through `Fintype.card_pos`.

| Object | Definition and check |
|---|---|
| `uniformMean f` | (Σ_M f M) / N. Each carrier is normalized by its own size. |
| `pairing Y M` | Σ_i Σ_j Y_ij·M_ij in ZMod 2, the Frobenius pairing tr(YᵀM). It is bilinear (`pairing_add_left/right`) and symmetric (`pairing_comm`). |
| `character Y M` | 1 if the pairing is 0, else −1, i.e. (−1)^{⟨Y,M⟩}. It is multiplicative in each argument: `bitSign_add` is proved by an exhaustive 4-case check, with 1+1=0 in ZMod 2. |
| Orthogonality | E[χ_Y·χ_Z] = [Y=Z]. Two cases: Y+Y = 0 gives χ₀ = 1 and mean 1. Otherwise there is a nonzero entry (i,j), and shifting by the matrix unit gives S = −S, so S = 0 (`linarith`). The dual version follows by `character_comm`. |
| `fourierCoeff f Y` | E[f·χ_Y], normalized. In particular f̂(0) = E f (`fourierCoeff_zero_frequency`). |
| Inversion | f = Σ_Y f̂(Y)·χ_Y, with no factor on the frequency sum. Check: N⁻¹ Σ_N f(N)·Σ_Y χ_Y(N)χ_Y(M) = N⁻¹ Σ_N f(N)·N·[N=M] = f(M). |
| `fourier_parseval` | E[f²] = Σ_Y f̂(Y)², with a normalized space measure and counting measure on frequencies. The proof writes f² = (Σ_Y f̂ χ_Y)·f, swaps the sums, and recognizes E[f·χ_Y] = f̂(Y). |
| `rankProjection i f` | Σ_{Y : Matrix.rank Y = i} f̂(Y)·χ_Y. Its coefficients are 1[rank Z = i]·f̂(Z) (`fourierCoeff_rankProjection`). Bessel gives E[(P_i f)²] ≤ E[f²]. The rank is the Mathlib `Matrix.rank`, which matches the MR-1 closure. |

**Agreement with the Full100 consumers.**
- `pairing_mul_right` decodes from its DAG as `pairing (Y*U) M = pairing Y (M*Uᵀ)`. That is exactly what the double-sum definition gives.
- The edges of `uniformMean_comp_equiv` (`Finset.sum`, `Fintype.card`, `Nat.cast`, `HDiv`, `ZMod.fintype`, `uniformMean._proof_1`) match the definition as sum divided by card.
- The edges of `character_mul_right` (`ite`, `Neg.neg`, `Real.instOne`, `ZMod.decidableEq`) match the if-then-else character.

**Spectral47 normalization.** Each carrier is normalized by its own size, and |Mat(n,c+s)| = |Mat(n,c)|·|Mat(n,s)|. So:
- (A_s(P_iF))^(Y) = 1[rank Y = i]·F̂([Y|0]), with no stray factor;
- post = Σ_{rank Y = i} F̂([Y|0])²;
- full = Σ_{rank Z = i} F̂(Z)².

The §5 injection route in the original reports is therefore consistent with this body's normalization.

**Other declarations in the file.** These are sound as written:
- the matrix-unit lemmas, `matrix_neg_self`/`matrix_add_self`, `rank_eq_zero_iff`, `fourierCoeff_add`/`rankProjection_add`;
- the restriction machinery (`AffineRestriction`, the nominal budget, the whole-space and exact restrictions);
- `binary_hc_rankZero[_exact]`, where the factor 2^{500·0²·p} equals 1 and δ ≤ δ^{1−2/p} for δ in [0,1];
- `binary_hc_rankLevel_L2_exact`.

Two non-claims notes:
- Despite the `binary_hc_*` names, nothing here proves positive-rank hypercontractivity. The file header says so correctly.
- `PseudorandomExact` counts nominal budget, so zero equations can pad a restriction up to exactly r. I make no fidelity claim about that against the manuscript.

## 3. Typed identities

**Source vs. object.** I checked the two categories separately and never compared one to the other.
- `BinaryMatrixFourier`: source 810324DD…70D8 (file header). Object `.olean` A8721515…E240 and `.olean.hash` 4F1D2794…8CB4 (inventory).
- No source SHA (810324DD, 409FD652, CF8990EA) appears among the inventory values. H1 stays closed.

**ADD-2.** The packet has no Full100 capture value for this source path to compare 810324DD… against: no `source-after.json` contents, no alignment-audit entry, no index row. So the supplied body is bound to object A8721515… only by consistency (the decoded consumer types and edges in §2), not by identity.

**Object matches against the original reports:**

| Module | Inventory `.olean` | Original reports | Match |
|---|---|---|---|
| RightOrbit | 79CC0A45…43F06972 | 79CC0A45…F06972 | Yes |
| RightFourierCovariance | EFF637A8…DC1B030 | 79… see note | Yes, against NC100's "…B030" |
| ManuscriptDyadicMoment | C02909B6… | C02909B6… | Yes |
| SourceSizeAnalyticMoment | B472BC2E… | B472BC2E… | Yes |

**ADD-4 (Info).** The complexity report abbreviates the RightFourierCovariance object as "EFF637A8…B1030". That does not match the real tail "…C1B030" as a string. It is a transcription slip inside an immutable report, not an identity defect: the prefix and the non-claims tail both agree with the inventory.

## 4. NC100-8: the 661 objects

- **Custody hashes agree.** The three native custody SHA fields and the terminal's `native_archive_sha256` are all 66BFF34B…8475. The three trace custody fields are all BB5288CA…9DE1.
- **Terminal receipt.** `probe_native_exit` is 0, `failure` is null, `compiled_objects_preserved` is 661, and `project_sources_preserved` and `project_object_closure` are both 327. The terminal itself also records `consumption_coverage_complete: false`, `reviewed: false` and `accepted: false`. It is a preservation receipt, not a coverage certificate (ADD-6).
- **No binaries archived.** The native archive member list has no `.olean` binaries. This is consistent with `compiled_object_binary_archive_claimed: false`.
- **The inventory does not split into pairs.** 661 is odd, so it cannot be uniform `.olean` + `.olean.hash` pairs. By my tally it is 331 `.olean` + 330 `.olean.hash`. `ActualBinaryMatrixHC46A7TransferOwnedChecks.olean` has no `.hash`.
- **There are more `.olean` files than closure modules.** I saw no hash without its `.olean`. So there are at least 331 `.olean` entries against a closure of 327: at least 4 compiled objects in the inventory are outside the 327-source closure. Because the expected 327-path list was not supplied, I cannot confirm the claim that every expected path is present. I can confirm the modules relevant here are present: RightOrbit, Covariance, Fourier, SameRangeOrbit, the SourceSize and Dyadic exports, and the bridge.

**Disposition:** the count is reconciled at the inventory/terminal tier. The residual is ADD-1 (Low): identify the surplus and unpaired objects. Fresh-checkout replay remains separate debt.

**ADD-3 (Low, pending disposition).** The member list shows `cslib-tracked-diff.patch` at 3,098,175 bytes, while every other package diff is 0 bytes. That means the cslib checkout differs from its pin. If any cslib file is in the 409-file external closure, pinned trust does not hold for it, and this rises to Medium.

**Info.** Each `stage-*.stderr` is 141 bytes. Their contents were not supplied.

## 5. CX100-12: the 12 nodes and 2 boundaries

The 12 nodes are the 8 new declarations, the 2 auxiliary proofs of `rightBasisEquiv`, and 2 external Mathlib theorems. That is exactly the 8 + auxiliaries + 2 externals the original reports inferred. The 2 new boundaries are the same 2 externals, which fits 8072 + 12 = 8084 and 2738 + 2 = 2740.

The checks behind the table:
- **Statements.** I decoded each statement from its DAG, resolving de Bruijn indices by binder depth.
- **Edges.** For each node I checked that the union edge list equals its type edges together with its proof edges.
- **No `sorryAx`.** None appears among the direct edges. Axiom profiles come from the receipts.
- **Digests.** I did not recompute the DAG digests.

| Node | Decoded statement / role | Key proof edges |
|---|---|---|
| `same_range_matrix_right_orbit` | ∀ M N : Mat(n,d), range toLin' M = range toLin' N → ∃ U V : Mat(d,d), U*V=1 ∧ V*U=1 ∧ N*U = M | `same_range_right_orbit`, `toMatrix'_comp`, `toMatrix'_id`, `toMatrix'_toLin'`, `LinearEquiv.symm` |
| `basis_invariant_eq_of_same_range` | ∀ {A : Type u₁} F hInv M N, equal ranges → F M = F N | the previous node |
| `rightBasisEquiv` (definition) | (U V : Mat(d,d)) → U*V=1 → V*U=1 → Mat(n,d) ≃ Mat(n,d) | `Equiv.mk`, the two `_proof`s |
| `rightBasisEquiv._proof_1` | U*V=1 → ∀ M, (M*U)*V = M (left inverse) | `Matrix.mul_assoc`, `Matrix.mul_one` |
| `rightBasisEquiv._proof_2` | V*U=1 → ∀ M, (M*V)*U = M (right inverse) | same |
| `pairing_mul_right` | pairing (Y*U) M = pairing Y (M*Uᵀ) | `Finset.sum_comm`, `sum_mul`/`mul_sum`, `ring` |
| `character_mul_right` | character (Y*U) M = character Y (M*Uᵀ) | `pairing_mul_right` |
| `uniformMean_comp_equiv` | uniformMean (H ∘ e) = uniformMean H | `Equiv.sum_comp` |
| `fourierCoeff_mul_right_of_basis_invariant` | hInv → U*V=1 → V*U=1 → F̂(Y*U) = F̂(Y), with hInv ranging over all M | `transpose_mul`, `transpose_one`, `rightBasisEquiv`, `uniformMean_comp_equiv` |
| `fourierCoeff_eq_of_same_range` | hInv → equal toLin' ranges → F̂ Y = F̂ Z | the two previous lemmas |
| `LinearMap.toMatrix'_id` (external) | toMatrix' id = 1 | `Matrix.ext`, `Pi.single_apply` |
| `Matrix.transpose_one` (external) | [DecidableEq n] [Zero α] [One α], (1 : Matrix n n α)ᵀ = 1 | `diagonal_transpose` |

**The two boundaries.**
- `toMatrix'_id`, in `Mathlib.LinearAlgebra.Matrix.ToLin`: its source is ToLin.lean. The proof-adversarial review read that file in full and re-derived this lemma, and the file is now bound to an index record (§6). **Disposition: reviewed.**
- `transpose_one`, in `Mathlib.Data.Matrix.Diagonal`: I verified its statement from the DAG, but the body is not supplied. **Disposition: pinned trust (ADD-5, Info).**

## 6. The three Mathlib sources in the index

The packet supplies explicit index records for:
- Rank.lean: 4CE45784…E262, 29,408 bytes;
- ToLin.lean: 9AEFBF5B…B1CD, 52,679 bytes;
- Finiteness.lean: 05316F2A…AC00, 4,050 bytes.

All three have revision e06eff5f…df2 and `complete_source: true`. Their SHA prefixes match the file headers quoted in the original reports (the reports only quoted prefixes). I accept the stated root verification against index 86C36CF4…. I cannot re-derive membership because the 409-entry listing itself was not supplied. **Closed at the record tier.**

## 7. Disposition of every original finding

| Original ID(s) | Disposition after this addendum |
|---|---|
| RO-1, RO-2, FC-1…6 / CX100-01…05 / NC100-1…3 | Verified. Unchanged. |
| MR-1 / CX100-06; CE-1 / CX100-07 | Closed. CE-1's Low debt (a matrix-form range lemma) remains. |
| ALN-1 | Closed (review). |
| **ALN-2 / NC100-7 / CX100-08** | **Body: closed** (§2). **Identity: open as ADD-2 (Low).** CX100-08's line numbers and its obsolete "frame pushforward" obligation are still open (Low). |
| **NC100-8** | **Reconciled** at the inventory/terminal tier. Residual: ADD-1 (Low). |
| **CX100-12** | **Closed.** All 12 nodes and both boundaries enumerated. Digests not recomputed. |
| The assumption that the three Mathlib files are in the 409-file index | **Closed** at the record tier. |
| SP-1 / CX100-10 / NC100-5 | Medium, open. |
| FID-1 / CX100-11 / NC100-6 | Open. |
| HY-1 / CX100-09 / NC100-4; N-4; other carried Lows | Low, open (hygiene). |
| Carried Mediums: numeric NO, `e`/`hfail`, joint witnesses, source/star/robust8S, pre-draw table, physical sampler | Open. |
| **R14** | **HIGH, open. Bars overall GO.** |

**New in this addendum:**
- ADD-1 (Low): surplus and unpaired objects in the inventory.
- ADD-2 (Low): the `BinaryMatrixFourier` source identity has no capture record to compare against.
- ADD-3 (Low, pending): the non-empty cslib diff.
- ADD-4 (Info): the transcription slip in the complexity report.
- ADD-5 (Info): the `transpose_one` boundary is pinned trust only.
- ADD-6 (Info): the trace terminal is not a coverage certificate.

## 8. Readiness

**Conditional integration.** This rests on pinned kernel and library trust, the receipts, typed identities and identity reuse. It remains GO-WITH-NOTES. This addendum closes evidence gaps and adds no HIGH, so the verdict is unchanged, not upgraded.

**What is now additionally supported:**
- The Fourier objects the covariance lemmas consume are freshly read, with the normalizations stated in §2.
- The trace additions are exactly the 12 named nodes.

**Overall readiness: not ready.** None of the following is claimed or follows from this addendum:
- universal Spectral47, or any unconditional theorem;
- a numeric NO bound;
- a source or runtime witness;
- a fresh-checkout replay;
- a compiled-object binary archive;
- manuscript fidelity;
- priority or publication;
- overall GO.

## Remaining to-do

1. **ADD-2:** supply the Full100 capture record for `BinaryMatrixFourier.lean` (the `source-after.json` row or the alignment-audit entry) and string-compare it against 810324DD…70D8.
2. **ADD-1:** supply the expected 327 `.olean` paths, identify the at least 4 surplus `.olean` entries, and explain why `ActualBinaryMatrixHC46A7TransferOwnedChecks.olean` has no `.hash`.
3. **ADD-3:** show that cslib is outside the 409-file closure, or review and disposition its 3 MB tracked diff.
4. **ADD-5:** supply `Data/Matrix/Diagonal.lean` from the index, or record `transpose_one` explicitly as pinned trust.
5. **Native Spectral47** via the injection route:
   - the product-mean lemma and the append coefficient identity;
   - the matrix-form range lemma (CE-1);
   - card Ω_Y = 2^{is};
   - both rank-level Parseval energies;
   - the gain bound and the rpow transfer;
   - the guarded inhabitant, transported through `spectral47_contract_iff`;
   - a consuming export that removes `hSpectral`, then a new trace and a fresh review.
6. Fidelity audit of the contract, including `PseudorandomExact`, against manuscript Lemma 4.7.
7. Update the CX100-08 obligation list (drop "frame pushforward"), and verify the audit line numbers.
8. Numeric NO with a useful `e`/`hfail`; the joint witnesses; source/star/robust8S; the pre-draw table; the physical sampler.
9. **R14:** encoded reduction and runtime, plus learning.
10. Upstream post-audit, then the exact CMMSA bridges.
11. Fresh-checkout replay with every hash recomputed, including the type-DAG digests of the 12 nodes.
12. Hygiene: the stale headers (HY-1 / NC100-4 / N-4), the legacy object field, superseding the m-coupled roots, and the warning debt.
13. Release: manuscript fidelity, novelty and citations, PDF, final providers.
