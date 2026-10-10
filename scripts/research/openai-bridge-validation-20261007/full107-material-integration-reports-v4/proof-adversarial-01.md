# Full107 proof-adversarial review: `ActualFiniteFrameProductDuality` and conditional material integration

The two new files are sound: I found no soundness, orientation, quantifier, cast or edge-case defect in any declaration. The exact s-factor product energy law is now kernel-checked. Overall GO is still barred, because R14 (encoded reduction and runtime) remains HIGH and other full-scope gates are open.

**How I reviewed.** I used no tools, wrote nothing, and ran no Lean, Lake or subagents. Hash checks are string comparisons of supplied values. Compile results, axiom profiles and trace facts come from the receipts.

## Verdicts

| Scope | Verdict |
|---|---|
| **Mathematical soundness** of the two fresh bodies (3 exported theorems, 7 private lemmas, Checks harness) | **Sound.** No defect found. |
| **Native translation** | **Closed for the exact s-factor product law**, guarded by `i ≤ c+s`. **Still open:** G/Φ completion and marginal laws, the Φ eigen-relation, the invariant-first adjoint, a packaged cross-level identity, and any complex-valued version. |
| **Conditional SourceSize/HC46/dyadic/selected-leaf integration** | **GO-WITH-NOTES.** The material bytes are unchanged. The new law runs alongside the material lane and does not feed it. |
| **Overall readiness** | **Not GO.** R14 is HIGH and open. The numeric, source, runtime, upstream, certification and publication gates are also open. |

## 1. Coverage

- **Fresh bodies, read line by line:**
  - `ActualFiniteFrameProductDuality.lean`, 7056 bytes, header 39E80A82…5DCE. This matches the capture pin and `source_sha256`; the object hash 6A0ADC71… matches the legacy field.
  - `ActualFiniteFrameProductDualityChecks.lean`, 385 bytes, DAF94EDB…532D. Its object hash 5E1E6799… matches.
- **Interfaces re-checked against supplied bodies:** `ActualFiniteFrameProductRatio`, `ActualFiniteAppendImageWeighted` (`frameProduct_scaled_le`), `ActualFiniteAppendSpectral47`, the legacy `AnalyticMoment` contract, `SourceSizeOriginalApplication`, `SourceSizeContractBridge`, `MatrixGrassmannIdentity`, and the `ActualFiniteAppendExactImageEnergyChecks` statement name.
- **Not in this packet:** the bodies of `GrassmannCounting` (which defines `frameProduct`) and `ActualFiniteAppendExactImageEnergy`.
  - The `frameProduct` shape, `∏ j : Fin k, (2^n − 2^j.val)` in ℕ, is corroborated three ways: `MatrixGrassmannIdentity.base_rank_ratio` (`Fin.prod_univ_eq_prod_range`), the `Fin.prod_univ_castSucc`/`succ` rewrites here, and `cast_frame`.
  - The `rw` that consumes the Full105 law succeeded natively, so its left-hand side matches syntactically.
- **Prior reports:** I read all 39, in the full text supplied in this packet.
- **Skipped required fresh bodies: none.**
- **Reuse, not rereading:** the other 344 parent bodies are credited by identity reuse only. I make no claim of a fresh rereading of all 346, and no claim about any body supplied only in packet 2.

## 2. Declaration audit

Notation: G(n,k) is `frameProduct n k` in ℕ, and d = c+s.

| Declaration | Check | Result |
|---|---|---|
| `frame_zero` (private) | If n < k, the factor j = n is 2ⁿ−2ⁿ = 0. | ✓ |
| `frame_pos` (private) | If k ≤ n, every j < k gives 2ʲ < 2ⁿ, so all factors are positive. | ✓ |
| `frame_append` (private) | `Fin.prod_univ_castSucc` gives G(n,k+1) = G(n,k)(2ⁿ−2ᵏ). | ✓ |
| `frame_diagonal` (private) | Split at index 0, then 2ⁿ⁺¹−2ʲ⁺¹ = 2(2ⁿ−2ʲ) via `Nat.mul_sub_right_distrib`, which is exact even under truncation. Result: G(n+1,k+1) = (2ⁿ⁺¹−1)2ᵏG(n,k). | ✓ |
| `width_shift` (private) | Uses s ≤ n+1, so 2ⁿ⁺¹−2ˢ = 2ˢ(2ⁿ⁺¹⁻ˢ−1). Combines `frame_append` with `frame_diagonal` and cancels 2ˢ > 0. Checked by hand: n=1, s=1 gives 3·1 = 1·3; s = n+1 gives 0 = 0. | ✓ |
| `frame_duality_nat` (private) | Induction on i, with c generalized. **i=0:** both sides are G(d,s). **i+1, c=0:** G(0,i+1) = 0, and G(s−(i+1), s) = 0 because s−(i+1) < s. **i+1, c+1:** two diagonal rewrites, then `width_shift`, then the IH. The `width` and `rank` rewrites are exact under i+1 ≤ c+1+s. Hand-checked (c,s,i) ∈ {(1,1,2), (2,1,1), (2,1,2), (1,2,1)}. | ✓ This is a counted equality in ℕ, not an assumed ratio. |
| **`frameProduct_ratio_duality`** | Both denominators are positive (i ≤ d and s ≤ d). `div_eq_div_iff` reduces the goal to the commuted ℕ identity. | ✓ |
| `cast_frame` (private) | Casts are taken factor by factor only when k ≤ n. `Nat.cast_sub` is used with 2ʲ ≤ 2ⁿ. | ✓ No truncated factor is cast. |
| **`frameProduct_ratio_eq_product`** | **i ≤ c:** s ≤ d−i, so both products cast exactly and `prod_div_distrib` applies. **i > c:** this forces s ≥ 1 and d−i < s. The ℕ count G(d−i,s) is 0, and the real factor j = d−i is (2^{d−i}−2^{d−i})/(…) = 0. The zero branch is explicit, not a 0/0 artifact. | ✓ |
| **`append_rank_projection_energy_eq_product`** | Rewrites the qualified Full105 law (ratio form) with the identity above. Real F; all-matrix paired-inverse `basisInv`; each carrier normalized by its own `uniformMean`; the actual unconditional `appendAverage`. | ✓ No Booleanity, rank filter on data, source-height or new analytic premise. |
| Checks harness | Contains only `#check` and `#print axioms`. Its output is build-log information, not evidence. | Info |

### Edge cases and orientation

| Case | Result |
|---|---|
| s = 0 | Forces i ≤ c. The product is empty (= 1), and the ratio G(c,i)/G(c,i) = 1 has a positive denominator. ✓ |
| c = 0, i ≥ 1 | Zero branch; both sides are 0. ✓ |
| i = 0 | Ratio 1/1, product ∏(2ᵈ−2ʲ)/(2ᵈ−2ʲ) = 1. ✓ |
| Zero width or n = 0 | Handled by the Full105 law: only rank 0 exists, and the energy is 0 otherwise. ✓ |
| i > n | Both energies are 0, so the identity is trivially true. ✓ |
| Real denominators | 2ᵈ−2ʲ > 0 for every j < s ≤ d, in both branches. ✓ |
| Exponent `c+s−i` | ℕ subtraction, exact under `hi`. ✓ |
| Orientation | Retained fraction G(c,i)/G(d,i) equals ∏_{j<s}(2^{d−i}−2^j)/(2^d−2^j), which is the manuscript's λᵢ. ✓ |
| Guard necessity | Without `hi`, s = 0 with i > c gives 0 (by total division) ≠ 1. The guard is retained in all three exports. ✓ |

## 3. The three exports as one milestone

The three exports chain correctly: count duality (ℕ, then ℝ), then the exact product, then the energy law. Together they give the exact equality

E_M[(A_s P_i F)²] = λᵢ · E_W[(P_i F)²], with λᵢ = ∏_{j<s}(2^{d−i}−2^j)/(2^d−2^j),

for every real F that is invariant under all paired-inverse right actions, and every i ≤ c+s.

| Status | Item |
|---|---|
| **Native now** | The diagonal energy equality in product form. |
| **Already native** | Cross-level vanishing for i ≠ j (Full90). The bound λᵢ ≤ 2^{−is} via `frameProduct_ratio_le` (Full103). |
| **Composable, not packaged** | ⟨T P_i F, T P_j F⟩ = δᵢⱼ λᵢ ‖P_i F‖². |
| **Argument-level only** | G/Φ, the completion count, uniform full-row-rank marginals, independent B/C sampling, the kernel-frame eigen-relation Φχ_Y = λᵢχ_Y, and the restricted adjoint. |

## 4. Integration (material bytes unchanged)

**Carried forward from earlier verified reviews:**
- `Instance N rows` is independent of the leaf arity m.
- One I, copies, U, A, C, T, f throughout, with one `Tc` serving `hfail`, the PR premise and the moment.
- c+s = 2h ≤ 2J, with `hdim`, `hD` and `hsmall` derived.
- `original_HC46_exact` is applied at `hEven := hsplit`.
- The caller chooses a dyadic k ≥ 4m.
- Full105 discharged Spectral47 in the SourceSize original and dyadic original exports. The remaining premises there are `hsel`, `hA`, `hrd`, `he`, `hfail` (on the same `Tc`) and `ha`.
- No uniform or rank-one surrogate, and no smaller source or star family.

**Two points the new law does not change:**
- **The material RHS is not tightened.** It still uses the factor 2^{−i(s−1)} + 3·2^{i−n}, because the product law is unconsumed by any material export.
- **The earlier real frame-ratio energy law** is restated, not newly established. It remains conditional on its explicit invariance, rank and carrier premises.

**What the product law does not supply:** source, selector, star or sampler witnesses.

**Bookkeeping:** checked or plausible.
- 257 + 3 = 260 roots; 89 + 3 = 92 focused; 344 + 2 = 346 sources; 695 + 4 = 699 objects.
- The trace grew by 29 nodes (to 8298) and by 5 external boundaries (to 2767). That is plausible for 3 roots, 7 private lemmas, auxiliaries and new Mathlib constants, but it is not enumerated.

## 5. Findings

| ID | Severity | Item | Disposition |
|---|---|---|---|
| D107-1 | Verified | All ten declarations | No action. |
| D107-2 | Info | `candidate.json` pins pre-repair bytes (FD14D19B…, 7058 B) and `native_verified: false` | Bounded smoke check only. The current bytes are 39E80A82… / 7056 B, and the repair is the documented `prod_div_distrib` change. The enumeration agrees with the identity but certifies nothing. |
| D107-3 | Low | Header says "Uncompiled successor candidate" | Stale against the receipts. Fix in the next revision; leave the immutable bytes as they are. |
| D107-4 | Info | The ℕ duality lemma is private | Optionally export it publicly for reuse. |
| D107-5 | Medium, open | G/Φ, adjoint, packaged cross-level identity | Prove natively, or keep explicitly argument-level in the manuscript. |
| D107-6 | Low/Medium, carried | Fidelity to Lemma 4.7, MZ24 A.13 | The cutoff is formally inert; the guards and +3 slack are unused. Word the exact λᵢ as a reconstruction: A.13 states only the weaker bound. No novelty is claimed. |
| F1-r | Low, carried | Legacy m-coupled and hHC-parametric exports still bind `hSpectral` | Supersede, or add discharged wrappers. |
| ID-tier | Low, carried | `GrassmannCounting` and `BinaryMatrixFourier` bodies; the Full104/106 diffs | Covered by identity reuse. Resolve during fresh-checkout replay. |
| **R14** | **HIGH, carried** | Encoded reduction and runtime | **Bars overall GO.** |

Carried Medium findings, all open: numeric NO (`hfail`, e, scalar parameters, effective L₀); the joint arity/source/selection/global-table witness; star, robust8S, pre-draw selection, sampling and the encoded reduction; learning; exact upstream transports; fresh source-object replay; inherited-warning certification.

## 6. Safe conditional claim

This rests on the pinned kernel and Init/Mathlib/Batteries, the 260 standard profiles, seven stage exits of 0, the 8298-node trace with zero unresolved entries, the typed identities, and identity reuse.

- **The new law.** For all n, c, s and i ≤ c+s, and every real F invariant under paired-inverse right actions, the post-append rank-i energy equals ∏_{j<s}(2^{c+s−i}−2^j)/(2^{c+s}−2^j) times the full rank-i energy. This includes a genuine zero when i > c and the empty product when s = 0.
- **Prior claims stand.** The Full105 SourceSize and dyadic material bounds hold with no HC46 or Spectral47 premise, conditional on `hsel`, `hA`, `hrd`, `he`, `hfail` and `ha`.

**Not claimed:**
- G/Φ, the adjoint, a complete cross-level or complex-valued manuscript law;
- numeric NO, witnesses, sampler, reduction, runtime or learning;
- upstream transports, fresh replay, or warning certification;
- citations, BibTeX, TeX, PDF or manuscript acceptance;
- novelty or priority.

## Remaining to-do

1. Native G/Φ completion and marginal laws, the Φ eigen-relation with independent B/C, the invariant-first adjoint, and a packaged cross-level identity; then an independent review.
2. Lemma 4.7 / MZ24 A.13 crosswalk: the inert cutoff, the unused guards, and reconstruction wording.
3. Supersede or wrap the spectral-conditional legacy exports (F1-r). Fix stale headers (D107-3) and flag labels.
4. Numeric NO: a certified scalar consumer (dyadic P ≥ max(4m, mT)), Parseval side conditions, a useful e with `hfail`, base and cutoff, and an effective L₀.
5. Joint I/copies/U/A/`hsel` witness; source, star and robust8S; the pre-draw global table; the physical sampler.
6. R14: encoded or implicit reduction with a runtime proof; learning.
7. Upstream post-audit, then the exact CMMSA transports.
8. Fresh-checkout replay with every hash and DAG digest recomputed, plus a fresh read of `GrassmannCounting`, `BinaryMatrixFourier` and `Diagonal`. Certify the inherited warnings.
9. Final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates.
