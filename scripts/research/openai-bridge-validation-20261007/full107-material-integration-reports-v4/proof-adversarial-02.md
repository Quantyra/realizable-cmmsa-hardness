# Full107 proof-adversarial review of the exact-product-energy files (`ActualFiniteFrameProductDuality` and its Checks)

I found no soundness, quantifier, orientation, normalization, cast or edge-case defect in either fresh body. The three public exports form one coherent milestone, but it is reached only in energy form. The material bounds still use the looser spectral factor. **R14 (HIGH) is still open, so I am not issuing an overall GO.**

## Verdicts

| Scope | Verdict |
|---|---|
| **Mathematical soundness** of `ActualFiniteFrameProductDuality.lean` (5 private lemmas, 3 exports) | **Sound.** Every declaration was re-derived; no defect. |
| **Checks harness** `ActualFiniteFrameProductDualityChecks.lean` | Inspected. It contains only `#check` and `#print axioms`, so it is build-log information, not evidence. |
| **Native translation** | **Done for the three stated exports**, each with the standard profile {propext, Classical.choice, Quot.sound}. The s-factor product law is now native **in projected-energy form**. Still not native: the Φ eigenvalue relation, the G/Φ completion and marginal laws, the restricted adjoint, and a packaged cross-level Gram identity. |
| **Conditional integration** (SourceSize, HC46, dyadic, selected leaf) | **GO-WITH-NOTES, conditional.** No HIGH is open in this scope. The material exports are byte-identical, and F1 stays discharged for the two spectral-discharged exports. The new product law feeds no material export. |
| **Overall readiness** | **No GO.** R14 (HIGH, encoded reduction and runtime) is open, along with the numeric-NO, source, sampler, upstream, certification and publication gates. |
| **Manuscript, novelty, priority** | No verdict and no acceptance. The append, Fourier and counting arguments are classical reconstructions. MZ24 Appendix A.13 states only the weaker bound. |

**Method.** I used no tools, made no writes, and ran no Lean, Lake or subagents. Every hash comparison below is a string comparison of values in the packet; I recomputed none. Compile results, axiom profiles, trace and custody come from the supplied receipts. Source and object hash categories are kept separate throughout.

## 1. Coverage

**Fresh complete bodies, both read in full, every declaration:**
- `ActualFiniteFrameProductDuality.lean`. Header 39E80A82…5DCE matches the capture pin (7056 bytes) and the typed `source_sha256`. The object hash is 6A0ADC71…0CFC1.
- `ActualFiniteFrameProductDualityChecks.lean`. Header DAF94EDB…532D matches the pin. The object hash is 5E1E6799…D093.

**Required fresh bodies skipped: none.**

**Parent interfaces re-checked against the fresh call sites (this packet):**
- `ActualFiniteAppendExactImageEnergy`: `append_rank_projection_energy_eq_frame_ratio`, along with its private `frameProduct_pos` and the per-image and rank-i equalities.
- `GlobalImageEnergy`, `ImageFibres` (`card_matrixImageFibre`), `ImageTailBridge`, `Spectral47ExactInhabitant` (restricted Parseval).
- `SourceSizeSpectralApplication`, `SourceSizeAnalyticMoment` and the dyadic exports.
- Mathlib `Fin.lean`: `Fin.prod_univ_castSucc` has the form (∏ f ∘ castSucc) · f(last); `Fin.prod_univ_succ` has the form f 0 · ∏ f ∘ succ. Both orientations match their uses.

**Inherited by identity only.** These are the other supplied parent and Complexitylib bodies in packets 1 and 2, plus the unsupplied bodies, covered by the 344-body / 8269-context reuse audit. I make no claim to have freshly reread all 346 bodies, and I make no claim about packet-1 bodies.

**Not supplied, so identity or pinned trust only:**
- `GrassmannCounting`, which defines `frameProduct`. Its definition as ∏_{j<k}(2^n − 2^j) in ℕ is consistent with `cast_frame` and with `ActualBinaryGrassmannSamplingBounds.cast_frameProduct`.
- `BinaryMatrixFourier`.
- Mathlib's `Finset.prod_div_distrib`.

**All 39 preserved reports were read.** Their findings and residues are retained (§5).

## 2. Declaration audit

Notation: G(n,k) = `frameProduct n k`, and d = c + s.

| Declaration | Re-derivation | Status |
|---|---|---|
| `frame_zero` (n < k ⇒ G(n,k) = 0) | The factor at j = n is 2ⁿ − 2ⁿ = 0. This is a genuine zero, not a truncation artifact. | Verified |
| `frame_pos` (k ≤ n ⇒ 0 < G) | For each j < k ≤ n, 2^j < 2^n, so every factor is positive. | Verified |
| `frame_append` | G(n,k+1) = G(n,k)·(2ⁿ − 2ᵏ), by `prod_univ_castSucc` with the last factor at index k. It holds for k > n as well; both sides are definitional unfoldings. | Verified |
| `frame_diagonal` | G(n+1,k+1) = (2ⁿ⁺¹ − 1)·2ᵏ·G(n,k). The j = 0 factor is 2ⁿ⁺¹ − 1. Each remaining factor is 2ⁿ⁺¹ − 2ʲ⁺¹ = 2(2ⁿ − 2ʲ) via `Nat.mul_sub_left_distrib`, which holds unconditionally in ℕ, so there is no hidden non-truncation premise. | Verified |
| `width_shift` (s ≤ n+1) | Combining `frame_append` with `frame_diagonal` gives G(n+1,s)(2ⁿ⁺¹ − 2ˢ) = (2ⁿ⁺¹ − 1)2ˢG(n,s). Factoring 2ⁿ⁺¹ − 2ˢ = 2ˢ(2ⁿ⁺¹⁻ˢ − 1) needs s + (n+1−s) = n+1, which is exactly the guard. Then cancel 2ˢ > 0. At the boundary s = n+1 both sides are 0. | Verified |
| `frame_duality_nat` (i ≤ c+s) | Proves G(c,i)·G(d,s) = G(d,i)·G(d−i,s) by induction on i with c generalized. **i = 0:** both sides are G(d,s). **i+1, c = 0:** G(0,i+1) = 0 and G(s−i−1,s) = 0, since s−i−1 < s by i+1 ≤ s. **i+1, c+1:** uses `frame_diagonal` on both rank counts, `width_shift` at (c+s, s) rewritten to c+1, and IH(c,i), whose guard i ≤ c+s follows. Index rewrites: c+1+s = c+s+1, and c+s+1−(i+1) = c+s−i. The `ring` steps treat the truncated differences only as identical atoms. Spot-checks: (c,s,i) = (1,1,1) gives 1·3 = 3·1; (2,1,2) gives 6·7 = 42·1. These match `candidate.json`. | Verified |
| `frameProduct_ratio_duality` | Both denominators are positive: G(d,i) > 0 from i ≤ d, and G(d,s) > 0 from s ≤ d. `div_eq_div_iff` reduces the claim to the cross-multiplied ℕ identity after a `mul_comm`, then cast via `exact_mod_cast`. The truncated d − i appears only as an index, never inside a cast. | Verified |
| `cast_frame` (k ≤ n) | `Nat.cast_sub` for each factor, justified by 2^j ≤ 2^n for j < k ≤ n. | Verified |
| `frameProduct_ratio_eq_product` | **Case i ≤ c:** s ≤ d − i, so every factor casts exactly. `prod_div_distrib` (the Full106 arity repair) gives ∏(aⱼ/bⱼ). **Case i > c:** G(d−i,s) is a genuine natural zero, since d−i < s. The real product has the factor at j = d−i < s equal to (2^{d−i} − 2^{d−i})/(2^d − 2^{d−i}), which is 0 by subtraction in ℝ. No truncated factor is cast individually. | Verified |
| `append_rank_projection_energy_eq_product` | Rewrites the Full105 law E_{Mat(n,c)}[(A_s P_iF)²] = (G(c,i)/G(d,i))·E_{Mat(n,d)}[(P_iF)²] into the product form. It holds for **arbitrary real F** with all-matrix paired-inverse invariance, under the actual unconditional append, with each carrier normalized by its own size. | Verified |

**Requested boundary checks:**

| Case | Result |
|---|---|
| i ≤ c + s | Required. Without it, s = 0 and i > c would give the ratio 0/0 = 0 against an empty product of 1. The guard is kept, as `argument.md` says. |
| i > c | Exact zero on both sides; the RHS zero comes from a real factor j = d−i < s. |
| s = 0 | The product is empty, equal to 1; the ratio is G(c,i)/G(c,i) = 1 under i ≤ c. |
| c = 0, i ≥ 1 | Covered by the i > c case. |
| i = 0 | Each factor is (2^d − 2^j)/(2^d − 2^j) = 1. |
| n = 0 | Does not enter the ratio. The energy side is the inherited Full105 law. |
| Denominators | 2^d − 2^j > 0 for j < s ≤ d. Natural denominators are positive from `frame_pos`. |
| Orientation | λ_i = ∏_{j<s}(2^{d−i} − 2^j)/(2^d − 2^j). This matches the manuscript formula and the kernel-frame count G(d−i,s)/G(d,s). |

## 3. Integration and the milestone

- **One milestone:** guarded duality, then the product identity, then the energy law. The three exports compose with no gap, and every guard kept is necessary.
- **Material lane unchanged.** The SourceSize, HC46 and dyadic exports are byte-identical. These all carry over:
  - independent `rows`;
  - one `Tc` in `hfail`, the PR premise and the moment;
  - derived `hdim`, `hD` and `hsmall`;
  - `original_HC46_exact`;
  - caller-chosen dyadic k ≥ 4m;
  - Spectral47 discharged in the two `…spectral_discharged` exports.
- **The product law is not consumed.** `selected_actual_analytic_rhs` still uses the factor 2^{−i(s−1)} + 3·2^{i−n}. Nothing has been tightened in the material bound.
- **No other change.** No uniform or rank-one substitute, smaller source or star family, or weaker helper has been introduced. No source, sampler or global-table witness is supplied.

## 4. Custody and bookkeeping

- **Typed pairs.** Duality: source 39E80A82… with object 6A0ADC71…. Checks: source DAF94EDB… with object 5E1E6799…. Each object matches its legacy field value. No source hash equals any object hash.
- **Historical candidate hash.** `candidate.json` lists the duality file as FD14D19B… at 7058 bytes. That is the pre-repair, uncompiled Full106 candidate; it differs by 2 bytes, consistent with the stated `prod_div_distrib` arity edit. I cannot diff the two without the old bytes (Info).
- **Counts are consistent:**
  - roots 257 + 3 = 260; focused 89 + 3 = 92; sources 344 + 2 = 346;
  - modules 216 + 1 = 217; objects 695 + 4 = 699;
  - trace 8269 → 8298 nodes (+29) and 2762 → 2767 boundaries (+5). That fits 3 roots, the private lemmas and auxiliaries, and new Mathlib constants (Fin products, `prod_div_distrib`, `mul_sub`). It is plausible but **not enumerated**.

## 5. Findings

| ID | Severity | Declaration | Disposition and action |
|---|---|---|---|
| FD-1 | Verified | `frame_zero`, `frame_pos`, `frame_append`, `frame_diagonal`, `width_shift` | None |
| FD-2 | Verified | `frame_duality_nat`, `frameProduct_ratio_duality` | None |
| FD-3 | Verified | `cast_frame`, `frameProduct_ratio_eq_product` (both branches) | None |
| FD-4 | Verified | `append_rank_projection_energy_eq_product` | It is energy form only. Do not cite it as the Φ eigenrelation. |
| FD-5 | Low (stale) | Module docstring says "Uncompiled successor candidate" | Contradicted by the receipts; fix in the next revision. |
| FD-6 | Info | Checks harness | `#print axioms` output is a log, not evidence. |
| FD-7 | Info (custody) | `candidate.json` FD14D19B vs. capture 39E80A82 | Historical pre-repair bytes. Supply the diff, or record it as receipt-tier. |
| FD-8 | Low (evidence tier) | `GrassmannCounting.frameProduct`, `Finset.prod_div_distrib` | Bodies not supplied. Read them freshly during replay. |
| FD-9 | Info | +29 nodes / +5 boundaries | Enumerate during fresh-checkout replay. |
| X3 / C105-05 / NC105-3 (carried) | Medium, narrowed | Exact operator route | The product energy law is now native. Still open: Φχ_Y = λ_iχ_Y, the GL completion and marginals, independent B/C sampling, the invariant-first adjoint, and the packaged ⟨T P_iF, T P_jF⟩ = δ_ij λ_i‖P_iF‖². Full90 orthogonality makes the last of these composable, but it is not packaged. |
| FID-1 / S1 / NC105-2 (carried) | Medium | Lemma 4.7 / A.13 crosswalk; inert cutoff | Manuscript wording must state that the exact eigenvalue is a reconstruction. |
| F1-r / C105-04 / NC105-1 (carried) | Low | Legacy m-coupled and hHC-parametric exports | Mark as superseded, or wrap. |
| Carried | Medium | Numeric NO and `hfail`/e/scalar; joint source, selection and global-table witnesses; joint arity; star and robust8S; pre-draw draws; sampling; encoded reduction; learning; upstream transports; fresh replay; inherited-warning certification | Open |
| **R14** | **HIGH** | Encoded reduction and runtime | Open. **Bars overall GO.** |

## 6. Safe conditional claim

This rests on pinned kernel and library trust, the 260 standard profiles, seven stage exits of 0, the qualified 8298-node trace with zero unresolved nodes, the typed identities, and identity reuse.

For all natural numbers c, s, i with i ≤ c + s:
- G(c,i)·G(c+s,s) = G(c+s,i)·G(c+s−i,s);
- G(c,i)/G(c+s,i) = ∏_{j<s}(2^{c+s−i} − 2^j)/(2^{c+s} − 2^j), including the zero branch when i > c.

For every real F invariant under all paired-inverse right actions, the actual unconditional append satisfies

  E[(A_s P_iF)²] = (∏_{j<s}(2^{c+s−i} − 2^j)/(2^{c+s} − 2^j)) · E[(P_iF)²].

**Not claimed:**
- the Φ eigenrelation, G/Φ laws, the adjoint, or a packaged cross-level identity;
- the complex-general energy law;
- Lemma 4.7 fidelity;
- source or sampler witnesses, numeric NO, or runtime;
- upstream transports, replay, or warning certification;
- novelty or priority;
- overall GO.

## Remaining to-do

1. Natively prove Φ P_iF = λ_i P_iF using the kernel-frame count: the GL completion and marginals, independent unrestricted B with full-row-rank C, the invariant-first adjoint, and the packaged cross-level Gram identity.
2. Do the Lemma 4.7 / MZ24 A.13 crosswalk: attribute the exact eigenvalue as a reconstruction, and address the inert cutoff and the unused guards and slack.
3. Decide whether to tighten the material RHS using the product law, or state explicitly that the looser factor is kept.
4. Supersede or wrap the legacy and hHC-parametric spectral-conditional exports.
5. Numeric NO: a certified scalar consumer, a useful e with `hfail`, B and Parseval side conditions, `base` and `cutoff`, and an effective L₀.
6. Joint I, copies, U, A and `hsel` witness; source, star and robust8S; the pre-draw global table; the physical sampler; encoded sampling.
7. R14: an encoded or implicit reduction with a runtime proof; learning.
8. Upstream post-audit, then the exact CMMSA transports.
9. Fresh-checkout and source-object replay, recomputing every hash and DAG digest: enumerate the +29/+5 delta, read `GrassmannCounting` and `prod_div_distrib` freshly, and supply the Full106→107 diff.
10. Hygiene: the FD-5 stale header, flag labels, the legacy hash field, and certification of inherited warnings.
11. Final provider, citation, BibTeX, TeX, PDF and manuscript gates.
