# Full107 non-claims review: exact product-form energy law (packet 1 of 2)

## Verdicts

| Scope | Verdict |
|---|---|
| **Is the math in the two fresh files sound?** (`ActualFiniteFrameProductDuality`, `…Checks`) | **Yes.** I found no soundness, orientation, quantifier, normalization, natural-to-real cast, zero-branch or vacuity defect. |
| **Are the three exports natively translated?** | **Yes, for exactly what they state.** The receipt gives all three a standard profile {propext, Classical.choice, Quot.sound}: frame-ratio duality, the s-factor product identity, and the product-form energy law for the unconditional append. |
| **Not natively translated** | The Φ eigen-relation, the G/Φ completion and marginal laws, the restricted adjoint, a packaged cross-level identity, complex-valued generality, and any cross-level translation. |
| **Conditional integration** | **GO-WITH-NOTES.** No HIGH finding in this scope. The product law is a standalone root. No material export uses it. |
| **Overall readiness** | **No GO.** R14 (HIGH) is still open, along with the numeric, source, runtime, upstream, certification and publication gates. |
| **Manuscript, novelty, priority** | **No acceptance.** |

**Method.** I used no tools, wrote nothing, and ran no Lean, Lake or subagents. Hash checks are string comparisons only. Kernel results, profiles, trace and custody come from the receipts.

**What I read.**
- **Both required fresh bodies: read in full, every declaration, nothing skipped.**
- **Other packet-1 bodies:** they are unchanged parent files. I read them at the interfaces the new file uses: `ActualFiniteFrameProductRatio`, `ActualFiniteAppendImageWeighted`, `…PerImageEnergy`, `ActualFiniteAppendSpectral47`, and the ExactImageEnergy checks harness. Beyond those interfaces, their semantic coverage is inherited per lens from the 39 preserved reports, matched by identity.
- **Not in this packet:**
  - The `ActualFiniteAppendExactImageEnergy` body, which the energy theorem rewrites with. It is presumably in packet 2. Full105 reviewed it, and here it is identity reuse only.
  - The `GrassmannCounting.frameProduct` definition. I infer it is ∏_{j<k}(2^n − 2^j) in ℕ from the `unfold` and `simpa` uses. That is identity tier.

  I am not claiming a fresh reread of all 346 sources. Full per-lens integration still needs the packet-2 report and a root reconciliation.

## 1. Custody of the fresh bodies

- **Main file.** The header SHA is 39E80A82…5DCE, 7056 bytes. It matches the capture pin and the typed `source_sha256`. The object is 6A0ADC71…0CFC1 and matches the legacy field.
- **Checks file.** Its header DAF94EDB… matches both the pin and `candidate.json`. The object is 5E1E6799….
- **Pre-repair candidate (NC107-1, Low).** `candidate.json` pins the main file at FD14D19B…, 7058 bytes, with `native_verified: false`. That is the pre-repair candidate. The 2-byte difference fits a dropped `" _"` in the `prod_div_distrib` arity repair, but the pre-repair bytes and the diff were not supplied, so this is inference. It does not affect the current receipt.
- **Count bookkeeping.** All of these add up:
  - Roots: 257 + 3 = 260; focused: 89 + 3 = 92.
  - Sources: 344 + 2 = 346; modules: 216 + 1 = 217 (the Checks file is not in the graph).
  - Objects: 695 + 4 = 699.
  - Nodes: 8269 + 29 = 8298; boundaries: 2762 + 5 = 2767. Neither the 29 new nodes nor the 5 new boundaries were enumerated.

## 2. Declarations, one by one

All seven private lemmas are correct over ℕ.

| Declaration | Check |
|---|---|
| `frame_zero` (n<k ⇒ G(n,k)=0) | The factor j=n is 2^n−2^n = 0, a genuine zero rather than a truncation artifact. |
| `frame_pos` (k≤n ⇒ G(n,k)>0) | Every j<k≤n has 2^j < 2^n. |
| `frame_append` | G(n,k+1) = G(n,k)·(2^n−2^k), splitting off the last factor. |
| `frame_diagonal` | G(n+1,k+1) = (2^{n+1}−1)·2^k·G(n,k). Each 2^{n+1}−2^{j+1} = 2(2^n−2^j) by `Nat.mul_sub_right_distrib`, which holds even when truncation gives 0 = 2·0. |
| `width_shift` (s≤n+1) | Equates the append and diagonal forms of G(n+1,s+1). Uses 2^{n+1}−2^s = 2^s(2^{n+1−s}−1) under the guard, then cancels the positive 2^s. |
| `frame_duality_nat` (i≤c+s) | **i=0:** 1·G = G·1. **i+1, c=0:** both sides have a zero factor. G(0,i+1)=0, and G(s−(i+1),s)=0 because the guard forces s≥1 and s−(i+1)<s. **i+1, c+1:** I re-derived it: diagonal on both sides, then `width_shift` at n=c+s (which rewrites c+s+1−s = c+1), then the IH at i ≤ c+s. Spot checks: (1,1,1) gives 1·3 = 3·1; (2,1,2) gives 6·7 = 42·1. Both agree with the bounded enumeration. |
| `cast_frame` (k≤n) | The factor-by-factor cast is valid because each 2^j ≤ 2^n. |

The three exports:

- **`frameProduct_ratio_duality`.** G(c,i)/G(c+s,i) = G(c+s−i,s)/G(c+s,s).
  - Both denominators are positive: i ≤ c+s and s ≤ c+s.
  - `div_eq_div_iff` is applied in the right orientation, after a single `mul_comm`.
  - c+s−i is exact under the guard.
  - The guard is essential. With s=0 and i>c, the left side is 0/0 = 0 and the right side is 1/1.
- **`frameProduct_ratio_eq_product`.**
  - **i≤c branch:** s ≤ c+s−i, so both products cast factorwise. Then `Finset.prod_div_distrib` (valid in ℝ) applies. Every real denominator 2^{c+s}−2^j with j<s is positive.
  - **i>c branch:** the guard forces s≥1, and j* = c+s−i < s. The natural count G(c+s−i,s) = 0. The real factor at j* is 0/(positive). The product uses real subtraction throughout, so factors with j>j* are negative reals, but the product is still exactly 0. No truncated factor is cast.
  - **Edge cases:** s=0 gives empty product 1 = G(c,i)/G(c,i) with i≤c. i=0 gives ratio 1, and every factor is x/x with x>0. c=0, i≥1 gives 0.
- **`append_rank_projection_energy_eq_product`.**
  - Statement: E_{Mat(n,c)}[(A_s P_iF)²] = λ_i·E_{Mat(n,c+s)}[(P_iF)²], where λ_i = ∏_{j<s}(2^{d−i}−2^j)/(2^d−2^j) and d = c+s.
  - It holds for any real F with all-matrix paired-inverse invariance (`basisInv`), with i ≤ c+s.
  - Each carrier is averaged over its own normalized uniform measure. The orientation is post = λ·full with λ ≤ 1, consistent with `frameProduct_ratio_le`.
  - The proof is two rewrites: Full105's frame-ratio law, then the product identity. Kernel acceptance confirms the interface matches.
  - Rows n=0, rank 0, and every zero-width case go through the Full105 law unchanged.
- **Checks harness.** It contains only `#check` and `#print axioms`. That is build-log info output, not evidence beyond the receipt.

## 3. Scope of what these three results are, and are not

These form one coherent milestone: ratio duality, then the exact product, then the energy law. Four limits apply.

1. **"Unconditional" refers to the append operator** (a uniform base plus a uniform appended block), not to the theorem. The theorem still needs `basisInv` and i ≤ c+s. It supplies **no source or sampler witness**.
2. **It is not the Φ eigen-relation** (Φχ_Y = λ_iχ_Y). It is also not the G/Φ laws, the invariant-first adjoint, the packaged identity ⟨T P_iF, T P_jF⟩ = δ_ij·λ_i‖P_iF‖², or a complex-valued statement. Cross-level vanishing is native separately (Full90), but nothing packages it with this law.
3. **It is not consumed.** The SourceSize, dyadic and spectral-discharged material exports are byte-identical. Their right-hand side still uses the weaker 2^{−i(s−1)} + 3·2^{i−n}. The material bound is not tightened.
4. **No novelty or priority claim.** This is a classical Gaussian/frame count with a Fourier argument. MZ24 A.13 states only the weaker bound. The exact identity is a reconstruction, not a quotation.

## 4. Findings

| ID | Severity | Location | Disposition |
|---|---|---|---|
| NC107-1 | Low (custody) | `candidate.json` (FD14D19B, 7058 bytes) vs pin (39E80A82, 7056 bytes) | Historical pre-repair record; the current receipt governs. Supply the arity-repair diff, or recompute it on replay. |
| NC107-2 | Low (stale text) | Header "Uncompiled successor candidate" | The immutable bytes contradict the receipt. Fix in the next revision. |
| NC107-3 | Info | Private `frame_zero`/`frame_pos` duplicate `FrameProductRatio` privates | Hygiene only. |
| NC107-4 | Medium (non-claim, carried) | Φ/G/adjoint/packaged cross-level/complex | Still open at argument level. Do not cite this law for them. |
| NC107-5 | Low/Medium (fidelity, carried) | Spectral47 contract; `sourceHeightCutoff` inert in the formal lane | Needs a Lemma 4.7 crosswalk. This law uses no source guards. |
| NC107-6 | Info (evidence tier) | ExactImageEnergy body and `frameProduct` def not in this packet | Identity reuse; packet 2 and replay. |
| NC107-7 | Info | Flags `material_body_review_complete` and `consumption_trace_complete` false | Historical. `source_selection_complete:false` is still current. |
| Carried | Low | Legacy `m`-coupled / hHC-parametric exports still spectral-conditional; stale banners; legacy hash field | Unchanged. |
| Carried | Medium | Numeric NO / hfail / e / scalar; source, selection and global-table witnesses; joint arity, star, robust8S, pre-draw, sampling; upstream transports | Open. |
| **R14** | **HIGH** | Encoded reduction / runtime / learning | Open. **Bars overall GO.** |

**Required fresh bodies skipped:** none. **HIGH in this scope:** none. **HIGH overall:** R14.

## 5. Safe claim

This rests on pinned kernel and library trust, the Full107 receipts (260 standard profiles, seven stage exits of 0), the qualified 8298-node trace with nothing unresolved, the typed identities, and identity reuse of the 344 parent bodies. Under those:

- For every n, c, s, i with i ≤ c+s, and every real F invariant under all paired-inverse right actions, the unconditional append satisfies:
  - E[(A_s P_iF)²] = ∏_{j<s}((2^{c+s−i}−2^j)/(2^{c+s}−2^j))·E[(P_iF)²], including the genuine zero branch for i > c;
  - G(c,i)/G(c+s,i) = G(c+s−i,s)/G(c+s,s).
- The Full105 SourceSize/dyadic material bounds, with HC46 and Spectral47 discharged, remain unchanged and conditional on the selector, failed-zoom and positivity premises.

**Not claimed:** source or sampler witnesses; numeric NO; G/Φ, the eigen-relation, the adjoint or complex generality; complete cross-level translation; an unconditional hardness result; inherited-warning certification; fresh replay; manuscript acceptance; novelty.

## Remaining to-do

1. Reconcile with the packet-2 report, and do the root per-lens reconciliation.
2. Supply the pre-repair→Full107 diff (NC107-1). On fresh-checkout replay, recompute the source, object and DAG hashes, enumerate the 29 new nodes and 5 boundaries, and read `GrassmannCounting` and `BinaryMatrixFourier` fresh.
3. Natively prove the Φ completion/marginal and eigen laws, the invariant-first adjoint, and a packaged cross-level identity. Alternatively, keep the manuscript limited to the energy law.
4. Lemma 4.7 / MZ24 A.13 crosswalk: the inert cutoff, the unused guards, and reconstruction-versus-quotation wording.
5. Supersede or discharge the legacy spectral-conditional exports. Clean up stale banners and the legacy hash field.
6. Numeric NO: hfail at a useful e, scalar parameters, base and cutoff, and an effective L₀.
7. Joint source/selection/global-table witness; joint arity; star/robust8S; pre-draw draws; sampling; encoded reduction.
8. R14: runtime proof; learning.
9. Exact upstream transports and post-objects.
10. Certify inherited warnings. Then the final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates.
