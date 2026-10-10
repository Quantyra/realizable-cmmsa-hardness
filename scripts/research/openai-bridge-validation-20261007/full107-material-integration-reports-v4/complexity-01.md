# Full107 complexity review: the exact product-energy milestone and conditional integration

## Verdicts

| Scope | Verdict |
|---|---|
| **Mathematics of the 2 new files** (`ActualFiniteFrameProductDuality`, its Checks file) | **Sound.** I found no defect in soundness, direction, quantifiers, normalization, natural-to-real conversion, edge cases or vacuity. I checked all 6 private lemmas and all 3 exported theorems. |
| **Native translation** | **Done for the three exports.** These are the frame-ratio duality, the exact s-factor product, and the product-form energy law for the actual unconditional append, all with standard axiom profiles. **Still open:** the eigenvalue law `Φχ_Y = λ_iχ_Y` (only its counting identity is native), G/Φ completion and marginals, the restricted adjoint, a single packaged cross-level identity, and any complex-valued version. |
| **Conditional SourceSize/HC46/dyadic/selected-leaf integration** | **GO-WITH-NOTES.** No HIGH finding in this scope. The material exports are byte-identical to Full105. The new law is a standalone root and nothing consumes it. |
| **Overall readiness** | **Not GO.** R14 (HIGH, encoded reduction and runtime) is still open, along with numeric NO, the witness, source, upstream, certification and publication gates. Nothing here is accepted as manuscript or publication content. |

**Method.** I used no tools, made no writes, and ran no Lean, Lake or subagents. Every hash check below is a string comparison of supplied values. Compile results, axiom profiles and trace facts come from the receipts. This is packet 1 of 2. A complete per-lens integration needs both packet reports plus the root reconciliation.

## 1. Coverage

| Body set | Status |
|---|---|
| `ActualFiniteFrameProductDuality.lean` (source 39E80A82…, 7056 bytes) | **Read line by line, every declaration.** |
| `ActualFiniteFrameProductDualityChecks.lean` (DAF94EDB…, 385 bytes) | **Read in full.** It contains only `#check` and `#print axioms`, so it produces info output, not evidence. |
| Parent bodies supplied in this packet | Re-checked fresh at the interfaces the new file touches: `ActualFiniteFrameProductRatio`, `ActualFiniteAppendImageWeighted` (frame counts), `ActualFiniteAppendSpectral47` (energy expansion), `ActualFiniteAppendImagePerImageEnergy`, both Spectral47 contract definitions, `SourceSizeContractBridge`, the SourceSize Original/Append/legacy Analytic moment exports, and Mathlib `ToLin`, `Rank`, `Finiteness`. |
| Other supplied parent bodies (Complexitylib, tagged/star/Cmmsa, sampling) | Present and unchanged. Their semantic credit comes from prior per-lens reviews matched by identity, **not from a fresh reread here.** |
| **Not supplied in this packet** | The body of `ActualFiniteAppendExactImageEnergy.lean` (only its Checks file is here), `GrassmannCounting` (`frameProduct`), and `BinaryMatrixFourier`. I credit the statement of `append_rank_projection_energy_eq_frame_ratio` through the Full105 reviews and the fact that the `rw` here type-checks. I did not freshly read these bodies. |

**Skipped required fresh bodies: none.** All 39 prior reports were read: Full90 packets ×15, Full90/95/97/100/103/105 integration ×18, Full95/100 addenda ×6.

## 2. Declaration audit

Below, `G(n,k) = ∏_{j<k}(2^n − 2^j)` in ℕ, consistent with every use in the file.

- **`frame_zero` (n<k ⇒ G = 0):** the factor at j = n is 2^n − 2^n = 0. This is a genuine zero factor, not a truncation artifact.
- **`frame_pos` (k ≤ n ⇒ G > 0):** for every j < k ≤ n we have 2^j < 2^n.
- **`frame_append`:** `G(n,k+1) = G(n,k)(2^n − 2^k)` by `Fin.prod_univ_castSucc`. Correct for all n and k.
- **`frame_diagonal`:** `G(n+1,k+1) = (2^{n+1}−1)·2^k·G(n,k)`. The j = 0 factor is 2^{n+1} − 1, and each later factor is 2^{n+1} − 2^{i+1} = 2(2^n − 2^i). That step uses `Nat.mul_sub_right_distrib`, which holds even under truncation, so it remains valid when i > n.
- **`width_shift` (s ≤ n+1):** `G(n+1,s)(2^{n+1−s}−1) = G(n,s)(2^{n+1}−1)`.
  - `append(n+1,s)` and `diagonal(n,s)` give two expressions for G(n+1,s+1).
  - The factor 2^{n+1} − 2^s = 2^s(2^{n+1−s} − 1) uses s ≤ n+1.
  - The common factor 2^s > 0 is then cancelled.
- **`frame_duality_nat` (i ≤ c+s):** `G(c,i)·G(c+s,s) = G(c+s,i)·G(c+s−i,s)`. Proof by induction on i with c generalized:
  - **i = 0:** both sides equal G(c+s,s).
  - **i+1, c = 0:** G(0,i+1) = 0. The guard forces s ≥ i+1, so s − (i+1) < s and the dual count is also 0.
  - **i+1, c+1:** uses the diagonal recurrence on both rank counts, `width_shift` at n = c+s (where c+s+1−s = c+1), and the induction hypothesis at (c,i). I rechecked the calc chain.
  - Spot checks: (c,s,i) = (1,1,1) gives 3 = 3; (2,1,2) gives 42 = 42; (0,2,1) gives 0 = 0.

### Exported theorems

- **`frameProduct_ratio_duality`:**
  - Both denominators are positive: G(c+s,i) because i ≤ c+s, and G(c+s,s) because s ≤ c+s.
  - `div_eq_div_iff` reduces it to the natural-number identity. `mul_comm` only reorders the right-hand side, and `exact_mod_cast` is a sound cast.
  - **The guard is necessary.** With s = 0 and i > c, the left side is 0/0 = 0 under Lean's division, but the right side is 1/1. The argument document states this correctly.
- **`cast_frame` (k ≤ n):** casts the product factor by factor. `Nat.cast_sub` is used only under 2^j ≤ 2^n, so no truncated factor is cast.
- **`frameProduct_ratio_eq_product`:**
  - **i ≤ c:** s ≤ c+s−i, so both frame products cast factor by factor. `(Finset.prod_div_distrib _ _).symm` then gives ∏(a_j/b_j). Every denominator 2^{c+s} − 2^j with j < s ≤ c+s is positive.
  - **c < i ≤ c+s:** the dual natural count is 0 because c+s−i < s. The real product contains the factor j = c+s−i, which is (2^{c+s−i} − 2^{c+s−i})/(…) = 0. Natural subtraction in the exponent is exact because i ≤ c+s.
  - **Edge cases:** s = 0 gives the empty product 1, and i ≤ c is forced. c = 0, i ≥ 1 gives 0. i = 0 gives 1, since every factor is d/d with positive d. The formula is independent of n.
  - **Orientation:** the numerator is 2^{d−i} (kernel dimension) and the denominator is 2^d, with d = c+s. This matches the argument's λ_i.
  - **Info:** in the zero branch, the real factors for j > c+s−i are negative. The product is still exactly 0, but the manuscript should not describe it as a product of nonnegative factors.
- **`append_rank_projection_energy_eq_product`:**
  - It is two rewrites on top of the Full105 frame-ratio energy law.
  - **Hypotheses:** arbitrary real F; `basisInv` over all matrices with paired two-sided inverses (deficient and zero matrices included); i ≤ c+s.
  - **Normalization:** each side uses its own carrier's `uniformMean`. The left side is the unconditional uniform base average plus the uniform appended-block `appendAverage`.
  - **Not assumed:** Booleanity, the source-height cutoff, ρ, parity, or rank conditioning of the sampled data.

## 3. Custody and bookkeeping

- **Typed identities.** The supplied header 39E80A82… equals the native `source_sha256` and the capture pin (7056 bytes). The object hash 6A0ADC71… equals the legacy `added_object_hashes` value. For the Checks file, DAF94EDB… pairs with 5E1E6799…. I never compared the source and object categories against each other.
- **Pre-repair candidate.** `candidate.json` lists the pre-repair bytes (FD14D19B…, 7058 bytes) with `native_verified: false`. That record is historical. The 2-byte difference fits the stated `prod_div_distrib` arity change (`_ _ _` → `_ _`), but I cannot diff the actual bytes. Its 30-case bounded enumeration is a smoke check only.
- **Counts:** 257+3 = 260 roots; 89+3 = 92 focused; 344+2 = 346 sources; 695+4 = 699 objects; 216+1 = 217 modules (the Checks file is not in the graph). Nodes rose by 29 and external boundaries by 5, which is plausible for new Mathlib lemmas such as `Fin.prod_univ_castSucc`, `Fin.prod_univ_succ`, `prod_div_distrib` and `div_eq_div_iff`. **These were not enumerated.**

## 4. Integration

- **SourceSize and dyadic exports are unchanged.** The bytes are identical, so they keep:
  - independent `rows` and leaf arity `m`;
  - the same `Tc` in `hfail`, the PR premise and the moment;
  - derived `hdim`, `hD` and `hsmall`;
  - `original_HC46_exact`;
  - caller-chosen dyadic `k ≥ 4m`;
  - Spectral47 discharged (the Full105 F1 closure);
  - the exact Grassmann center normalization;
  - character pairing, tail-zero, orbit and counting route, and the weaker `+3` contract.
- **No consumer for the product law.** `selected_actual_analytic_rhs` still uses `2^{−i(s−1)} + 3·2^{i−n}`. The exact product does not tighten any material bound, and nothing claims it does.
- **No new witnesses.** The product law supplies no source, sampler, selection or global-table witness, and changes nothing about runtime.

## 5. Findings

| ID | Severity | Declaration | Disposition and action |
|---|---|---|---|
| C107-01 | Verified | 3 exports and 6 private lemmas | Sound and native. |
| C107-02 | Info | `frameProduct_ratio_duality` guard | `i ≤ c+s` is essential and is kept. |
| C107-03 | Info | zero branch of the product | Factors can be negative; the product is exactly 0. Wording action for the manuscript. |
| C107-04 | Low (stale) | Duality header "Uncompiled successor candidate…" | Contradicted by the receipt. Fix in the next revision; inputs stay immutable. |
| C107-05 | Medium (open; narrows C105-05, X3, NC105-3) | Exact operator route | The λ_i product is now native. Still to do: the Φ eigenvalue with independent B/C, GL completion and marginals, the invariant-first adjoint, and the packaged ⟨T P_iF, T P_jF⟩ identity. |
| C107-06 | Low | Hash of the pre-repair candidate | Supply the Full106→107 diff, or record it as receipt-tier. |
| C107-07 | Low (evidence tier) | `ExactImageEnergy`, `GrassmannCounting` and `BinaryMatrixFourier` bodies not in this packet | Identity reuse only. Confirm against packet 2 and the root reconciliation. |
| Carried, Low | — | legacy hSpectral exports (F1-r); stale banners; flag labels; legacy hash field; inherited warnings | Unchanged. |
| Carried, Medium | — | numeric NO/`hfail`/`e`/scalar; joint witnesses; source, star, robust8S, pre-draw, sampling; Lemma 4.7 / A.13 crosswalk; upstream transports | Unchanged. |
| **R14** | **HIGH** | encoded reduction and runtime | Open. **Bars overall GO.** |

## 6. Safe conditional claim

This rests on pinned kernel and library trust, 260 standard profiles, seven stage exits of 0, the GREEN trace with zero unresolved entries, and identity reuse.

For every n, c, s, i with i ≤ c+s, and every real F invariant under all paired-inverse right actions:

  E[(A_s P_iF)²] = ∏_{j<s} (2^{c+s−i} − 2^j)/(2^{c+s} − 2^j) · E[(P_iF)²],

and this equals G(c,i)/G(c+s,i). It is 0 when i > c and 1 when s = 0 or i = 0. The Full105 Spectral47-free SourceSize and dyadic material bounds remain unchanged.

**Not claimed:**
- a complex-general law, G/Φ, the adjoint, or the operator eigenvalue law;
- source or sampler witnesses, numeric NO, runtime or learning;
- upstream transports, replay, or warning certification;
- novelty or priority (the counting argument is classical; MZ24 A.13 states only the weaker bound);
- manuscript acceptance or overall GO.

## Remaining to-do

1. Packet 2 report, then root reconciliation across both packets.
2. Native Φ eigenvalue law, G/Φ completion and marginals, restricted adjoint, and a packaged cross-level identity, each independently reviewed.
3. Lemma 4.7 / MZ24 A.13 crosswalk: exact eigenvalue presented as a reconstruction, wording for the zero branch, and the inert cutoff and `+3` slack.
4. Supersede or wrap the legacy hSpectral exports (F1-r). Fix stale headers and flags. Supply the Full106→107 diff.
5. Numeric NO: certified scalar consumer and `hfail` at a useful `e`.
6. Joint witness for I, copies, U, A and hsel. Source, star, robust8S, pre-draw global table, physical sampler.
7. R14: encoded or implicit reduction with a runtime proof; learning.
8. Upstream post-audit, then exact CMMSA transports.
9. Fresh-checkout and source-object replay recomputing all hashes and DAG digests. Fresh reads of `GrassmannCounting`, `BinaryMatrixFourier` and `ExactImageEnergy`. Inherited-warning certification.
10. Final provider, citation, BibTeX, TeX, PDF and manuscript gates.
