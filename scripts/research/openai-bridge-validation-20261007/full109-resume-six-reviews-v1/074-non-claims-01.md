# Full109 non-claims review, packet 1 of 2: cross-level identity and material integration

The two fresh bodies are sound. The cross-level identity and its integration are **GO-WITH-NOTES, conditional**, with no HIGH finding in this scope. **Overall GO is not issued**: R14 is still HIGH, and every other remaining gate is still open.

I used no tools, writes, Lean, Lake or subagents. Every hash check below is a string comparison of values supplied in the packet. Compile results, axiom profiles, trace and custody come from the receipts. This is packet 1 of 2: a per-lens integration verdict also needs the packet-2 report and the root reconciliation.

## Verdicts

| Scope | Verdict |
|---|---|
| **Fresh bodies**: `ActualAppendProductCrossLevelIdentity.lean` and its Checks file | **Sound.** No defect in soundness, direction, quantifiers, normalization, guards or edge cases. |
| **Native translation of the exact real same-function cross-level Gram identity** | **Achieved, exactly as stated.** One root has a standard profile {propext, Classical.choice, Quot.sound}. 261 roots, focused set of 93, 348 sources, 8299 nodes, 0 unresolved. |
| **Conditional real cross-level acceptance** | **GO-WITH-NOTES.** It rests only on two prior native results: the Full107 product-energy law (reviewed in three lenses) and the Full90 orthogonality result. |
| **Integration into selected-leaf, SourceSize, HC46, dyadic and material callers** | **GO-WITH-NOTES, unchanged.** No caller consumes the new root. The caller bytes and hypotheses are the same as before. |
| **Overall readiness / manuscript** | **NO-GO.** R14 (HIGH) is open, along with every gate listed in the to-do. Nothing is accepted for the manuscript, novelty or priority. |

## 1. Coverage and skips

**Fresh, read line by line (nothing skipped):**
- **Main file.** Source header BB738BC9…CE90 equals the native `source_sha256`. Its object 5E713CCE… equals the legacy field, and the categories are never crossed. The declarations are one theorem plus namespace and `open` boilerplate.
- **Checks file.** Header 113B8DDB…0739 matches the record. The file contains only `#check` and `#print axioms`, so it is information, not evidence.

**Interfaces re-checked against the fresh call sites (bodies supplied in this packet):**
- `ActualAppendFourierCrossLevelOrthogonality`: `uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero`. I checked its binders `{n c s i j} (hij : i ≠ j) F` and that its conclusion matches the off-diagonal goal exactly.
- `ActualFiniteAppendSpectral47`, `ExactInhabitant`, `PerImageEnergy`, `ImageWeighted`, `FrameProductRatio`, `OrbitFourier`.
- The legacy `AnalyticMoment` and `HC46OriginalApplication` contracts and exports.

**Not in this packet, so not freshly re-read here:**
- `ActualFiniteFrameProductDuality.lean`, the source of `append_rank_projection_energy_eq_product`, which the diagonal branch consumes.
- The `ActualFiniteAppendExactImageEnergy` body; only its Checks file is here.
- The SourceSize, Dyadic and SourceSizeSpectralApplication bodies, `BinaryMatrixFourier` and `GrassmannCounting`.
- The definitions of `ite_eq_left` and `ite_eq_right`.

For the diagonal statement I rely on two things. The kernel accepted the `simpa only [pow_two]` match, and the Full107 reports record that same statement for the theorem. For `ite_eq_left : c → ite c a b = a` and `ite_eq_right : ¬c → ite c a b = b`, the signatures are corroborated by how pinned parents use them (Cheeger, `ActualCmmsaParameterReconciliation`, `Ring/Finset`).

**Identity reuse.** The 346 parent bodies are reused by identity only, with 8298 shared nodes. That is not a fresh read of all 348 bodies.

**Reports.** I read all 45 preserved reports: Full90 (15 + 3), Full95/97/100 and their addenda (15), Full103 (3), Full105 (3), Full107 (6). Their findings and residues are carried forward below.

## 2. Declaration audit: `append_rank_cross_level_gram_eq_product`

**Hypotheses.**
- Natural numbers n, c, s, i, j, with `hi : i ≤ c+s` only.
- An arbitrary real-valued F on `BinaryMatrix n (c+s)`.
- `basisInv`: invariance under paired inverses over **all** matrices, with the original binder order.
- No bound on j. No Booleanity, source height, ρ or parity condition, and no rank conditioning of the sampled data.

**Conclusion.** It is an exact if-then-else equality:

> E_{M∈Mat(n,c)}[A_s P_iF · A_s P_jF] = **if** i = j **then** ∏_{k<s}(2^{c+s−i}−2^k)/(2^{c+s}−2^k) · E_{W∈Mat(n,c+s)}[(P_iF)²] **else** 0

- Each mean is normalized over its own carrier.
- A_s is the actual unconditional `appendAverage`.
- The same F appears in both factors.
- It is not weakened to an inequality.

**Proof, case i = j.**
1. `subst j`, then `rw [ite_eq_left rfl]` selects the then-branch.
2. `simpa only [pow_two]` rewrites both sides of the Full107 law uniformly. It only touches the literal `^2`; the `2^(c+s−i)` factors are untouched.
3. The `hi` guard is consumed exactly where Full107 needs it.

**Proof, case i ≠ j.** `rw [ite_eq_right hij]` and then the Full90 zero theorem. That theorem needs neither `basisInv` nor `hi`, so the off-diagonal zero holds for every real F and every i ≠ j. No j bound is needed, and the theorem correctly omits one.

**Edge cases.**

| Case | Result |
|---|---|
| i > c (with i ≤ c+s) | The factor at k = c+s−i < s is (x−x)/(positive) = 0. Truncated subtraction is exact under `hi`. Factors with k > c+s−i are negative reals, but the product is exactly 0. |
| s = 0 | `Fin 0` gives the empty product 1, and `hi` forces i ≤ c. The guard is essential: without it the Full107 ratio form would read 0/0 = 0, not 1. |
| i = 0 | Every factor is x/x with x = 2^{c+s}−2^k > 0, so the coefficient is 1. |
| n = 0 or zero width | These go through the inherited laws (single-element carriers). |
| Empty rank-i support (i > n) | Both sides are 0. |
| j > c+s | P_jF = 0, which agrees with the 0 branch. |

## 3. Integration

- **No consumer.** No SourceSize, HC46, dyadic, selected-leaf or material export consumes the new root. The selected-leaf high-energy path already used Full90 orthogonality (`appendHighLevel_energy_eq_sum`). The material RHS keeps the weaker 2^{−i(s−1)} + 3·2^{i−n}. Nothing is tightened, and no claim of tightening may be made.
- **Prior caller hypotheses stay exactly as before.** The SourceSize/dyadic Spectral47-discharged exports remain conditional on `hsel`, `hA`, `hrd`, `he`, `hfail` (on the same `Tc`) and `ha` (plus `hkDyadic` and `hkm`). The legacy m-coupled and hHC-parametric exports still take `hSpectral` (F1-r).
- **Repair claim.** The Full109 change from the Full108 candidate is described as replacing the deprecated `if_pos`/`if_neg` aliases with `ite_eq_left`/`ite_eq_right`, with headers unchanged. The fresh bytes fit that description: there is no `set_option linter`, and the receipts show 0 owned warning headers and 0 inherited-regression headers. However, the old bytes (B3F1C4F5…) and the diff were not supplied, so this rests on the receipt only. Inherited warning debt is not certified by it.
- **Bookkeeping.** 260+1 = 261 roots, 92+1 = 93 focused roots, 346+2 = 348 sources, nodes +1 to 8299, 2767 boundaries unchanged. That is plausible, because `ite_eq_*` and `pow_two` were already reached through other modules. It is not enumerated.

## 4. Findings

| ID | Severity | Location | Disposition and action |
|---|---|---|---|
| X109-1 | Verified | `append_rank_cross_level_gram_eq_product` | Exact, sound, native. Conditional real cross-level milestone accepted. |
| X109-2 | Low (stale) | Module docstring: "This successor candidate has not been compiled" | Contradicted by the native receipt. Fix in a later revision; these bytes stay immutable. |
| X109-3 | Low / Medium (non-claim wording) | Statement form | The diagonal-δ form equals the manuscript's λ_j⟨P_iF, P_jF⟩ only together with pre-append rank orthogonality ⟨P_iF, P_jF⟩ = δ_ij‖P_iF‖², which no theorem packages. Do not cite this theorem as the λ_j-inner-product form without that lemma. |
| X109-4 | Info | `hi` guard is asymmetric | Callers with i > c+s ≥ j must swap the arguments; the result is symmetric. No caller loses anything. |
| X109-5 | Info | `if i = j` uses `instDecidableEqNat` | Consumers that work under `Classical.propDecidable` may need `if_congr`. Hygiene only. |
| X109-6 | Info (custody) | Full108 bytes and diff | Receipt tier only. Supply them, or recompute during replay. |
| X109-7 | Info (evidence tier) | Duality, ExactImageEnergy, SourceSize, Fourier and GrassmannCounting bodies are absent from packet 1 | Covered in packet 2 or by identity reuse. Reconcile at the root. |
| X109-8 | Info | Checks harness | Information output only. |
| Carried | Medium (open) | Native G/Φ completion and marginals, independent B/C sampling, the pointwise Φ eigen-relation, the restricted invariant-first adjoint, two-function and complex extensions | **None of these is proved.** This theorem is a direct derivation and does not use or establish the adjoint. |
| Carried | Medium | Lemma 4.7 / MZ24 A.13 crosswalk | Inert cutoff; exact λ_i described as a reconstruction; zero-branch wording with negative factors. |
| Carried | Medium | Numeric NO, `hfail`/e/scalar, source-height fidelity; joint source, selection and global-table witnesses; star/robust8S; pre-draw draws; sampler; encoded reduction; learning; exact upstream transports and post-objects | Open. **No witness of any kind** comes from this theorem. |
| Carried | Low | F1-r; stale banners; flag labels; legacy hash field; 566/699+ object reconciliation; fresh-checkout source and object replay; certification of inherited warnings | Open. |
| **R14** | **HIGH** | Encoded reduction and runtime | Open. **Bars overall GO.** |

## 5. Safe claim

This rests on pinned kernel and library trust, the Full109 receipts (261 standard profiles, seven stage exits of 0, an 8299-node trace with nothing unresolved, terminated custody) and identity reuse of 346 bodies. Under those:

> For all n, c, s, i, j with i ≤ c+s, and every real F invariant under paired-inverse right actions on all matrices, the unconditional append satisfies:
>
> E[A_sP_iF · A_sP_jF] = [i = j] · ∏_{k<s}(2^{c+s−i}−2^k)/(2^{c+s}−2^k) · E[(P_iF)²].

The earlier conditional material bounds are unchanged.

**Not claimed:**
- G/Φ composition, sampling laws, the eigen-relation, the adjoint, two-function or complex versions;
- a tightened material RHS;
- numeric NO or any source, selection, global-table, star, robust8S, pre-draw, sampler, reduction, runtime or learning witness;
- upstream transports, replay, or warning certification;
- provider, novelty, citation or manuscript acceptance;
- overall GO.

## Remaining to-do

1. Packet-2 report, then root reconciliation across both packets for every lens.
2. Supply the Full108 bytes and diff, or record them as receipt tier.
3. Natively prove the GL completion counts and uniform marginals, the Φ law with independent unrestricted B and full-row-rank C, the kernel-frame eigen-relation, and the invariant-first restricted adjoint. Then the packaged λ_j⟨P_iF, P_jF⟩ form (X109-3), then the two-function and complex extensions, each with independent review.
4. Lemma 4.7 / MZ24 A.13 crosswalk and manuscript wording.
5. Supersede or wrap the legacy spectral-conditional exports (F1-r). Fix the stale header X109-2 and the flag labels.
6. Numeric NO: certified scalar consumer, `hfail` at a useful e, source-height fidelity, an effective L₀.
7. Joint source, selection and global-table witnesses; joint arity; star/robust8S; pre-draw draws; physical sampler.
8. R14: encoded or implicit reduction with a runtime proof; learning.
9. Exact upstream transports and post-object audit.
10. Fresh-checkout source and object replay recomputing every hash and DAG digest; fresh reads of Duality, ExactImageEnergy, `BinaryMatrixFourier` and `GrassmannCounting`; certification of inherited warnings.
11. Final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates.
