# Full107 complexity-lens review, packet 2 of 2: the exact product-energy milestone and conditional material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **Mathematical soundness** of `ActualFiniteFrameProductDuality.lean` and its Checks file | **Sound.** I checked all 10 declarations: 3 exports and 7 private lemmas. I found no defect in soundness, orientation, truncated subtraction, casts, quantifiers, normalization or vacuity. |
| **Native translation** | **Closed for the three exports**, each with a standard profile per the receipt: frame-ratio duality, the s-factor product identity, and the unconditional append product-form energy law. **Still open:** the Φ eigen-relation itself, G/Φ completion and marginals, independent B/C sampling, the invariant-first adjoint, a packaged cross-level identity, and complex generality. |
| **Conditional SourceSize/HC46/dyadic/selected-leaf integration** | **GO-WITH-NOTES.** Nothing in this scope changed. The Full105 spectral-discharged exports and the closure of F1 stand. The new roots are not consumed by any material export. |
| **Overall readiness** | **Not GO.** R14 (encoded reduction and runtime) is still an open HIGH. The numeric-NO, witness, source/star/sampler, upstream, certification and publication gates are also open. There is no manuscript acceptance and no novelty claim. |

**Method.** I used no tools, wrote nothing, and ran no Lean or Lake. Every hash comparison is a string comparison of values supplied in the packet; I recomputed none.

**Packet scope.** This is packet 2 of 2. A full per-lens integration verdict needs both packet reports plus the root reconciliation.

## 1. Coverage

**Read fresh, every line (nothing skipped):**

| File | What I checked |
|---|---|
| `ActualFiniteFrameProductDuality.lean` | Header 39E80A82…DCE equals the capture pin (7056 bytes) and the typed `source_sha256`. Object 6A0ADC71… equals the legacy field. |
| `ActualFiniteFrameProductDualityChecks.lean` | Source DAF94EDB…32D and object 5E1E6799…093 both match. The file contains only `#check` and `#print axioms`, so it produces info output, not evidence. |

**Re-checked at the interfaces the fresh file uses:**

- **Mathlib.** `Fin.prod_univ_castSucc` and `Fin.prod_univ_succ`. Both statements in the supplied `BigOperators/Fin.lean` match how the fresh file uses them.
- **Full105.** `append_rank_projection_energy_eq_frame_ratio` and the private `frameProduct_pos` in `ActualFiniteAppendExactImageEnergy`.
- **Full105 consumers.** The `ActualSelectedComplementSourceSizeSpectralApplication` wrappers.
- **Material lane.** The SourceSize/Dyadic export binders, `spectral47_exact_contract_inhabitant`, `SourceSizeContractBridge`, and the `GlobalImageEnergy` partition lemmas.

**Inherited, not re-derived:**

- The remaining supplied bodies (about 46 project, Complexitylib and Mathlib files) are byte-identical. I read them at their interfaces only. Their semantic credit comes from per-lens identity reuse across the 39 prior reports.
- The other 344 parent sources and 8269 parent dependency nodes are covered by the identity audit. That is not a fresh reading of all 346 bodies, and I make no such claim.

**Not in this packet:** the body of `GrassmannCounting.frameProduct`. Its shape, `∏ j : Fin k, (2^n − 2^j)` in ℕ with truncated subtraction, is consistent with every use I can see, including `cast_frameProduct` in `ActualBinaryGrassmannSamplingBounds`. I take it at the identity-reuse tier. Also absent: the Mathlib `BigOperators/Field` body behind `Finset.prod_div_distrib`, which is pinned trust.

**Skipped required fresh bodies: none.**

**Bookkeeping is consistent:**
- Sources 344+2 = 346; roots 257+3 = 260; focused set 89+3 = 92.
- Modules 216+1 = 217 (the Checks file is not in the graph); objects 695+4 = 699.
- Nodes 8269 → 8298 (+29) and boundaries 2762 → 2767 (+5) are plausible for 3 roots, 7 private lemmas, auxiliaries and new Mathlib constants such as `Fin.prod_univ_*`, `prod_div_distrib` and `div_eq_div_iff`. Neither delta is enumerated (finding PD-8).

## 2. Declaration audit

Below, G(n,k) means `frameProduct n k`.

| Declaration | Re-derivation | Status |
|---|---|---|
| `frame_zero` (n<k) | Factor j=n gives 2ⁿ−2ⁿ = 0. | ✓ A genuine zero factor, not a truncation artifact. |
| `frame_pos` (k≤n) | Every j<k≤n has 2ʲ<2ⁿ, so each factor is positive. | ✓ |
| `frame_append` | Split at `last`: G(n,k+1) = G(n,k)(2ⁿ−2ᵏ). The `castSucc`/`last` values are j and k. | ✓ Holds unconditionally, zero factors included. |
| `frame_diagonal` | Split at 0: the first factor is 2ⁿ⁺¹−1, and each later factor is 2ⁿ⁺¹−2ʲ⁺¹ = 2(2ⁿ−2ʲ). That uses `Nat.mul_sub_right_distrib`, which holds exactly in ℕ, so there is no hidden non-truncation premise. The constant factor gives 2ᵏ. | ✓ |
| `width_shift` (s≤n+1) | 2ⁿ⁺¹−2ˢ = 2ˢ(2ⁿ⁺¹⁻ˢ−1), where `pow_add` needs s≤n+1. Combine append(n+1,s) with diagonal(n,s) and cancel the positive 2ˢ. | ✓ The edge s=n+1 gives 0=0. |
| `frame_duality_nat` | Induction on i, generalizing c. **i=0:** both sides are G(c+s,s). **c=0, i+1:** both sides are 0, because 0<i+1 and s−(i+1)<s (the latter needs i+1≤s). **c+1, i+1:** diagonal applied to both rank counts, then width_shift at n=c+s, then the IH at (c,i). The `ring` steps treat truncated terms as atoms, and `c+s+1−(i+1) = c+s−i` is valid under the guard. | ✓ I also spot-checked (c,s,i) = (2,1,1): 21=21; (2,1,2): 42=42; (1,1,2): 0=0. |
| `frameProduct_ratio_duality` | Both denominators are positive under i≤c+s and s≤c+s. `div_eq_div_iff` reduces the goal to a cross-multiplication; a single `mul_comm` rewrite hits the intended right-hand occurrence; cast. | ✓ |
| `cast_frame` (k≤n) | Each `Nat.cast_sub` is applied only under 2ʲ≤2ⁿ. | ✓ No invalid factorwise cast. |
| `frameProduct_ratio_eq_product` | **Case i≤c:** s ≤ c+s−i, so both products cast factor by factor, then `prod_div_distrib` (an unconditional identity in ℝ). **Case c<i≤c+s:** the natural-number G(c+s−i,s) is 0, and on the right the real factor at j = c+s−i < s is (x−x)/y = 0. | ✓ Handles s=0 (empty product = 1 = 1/1), c=0, and i=0. |
| `append_rank_projection_energy_eq_product` | Rewrites the native Full105 frame-ratio law with the product identity. Hypotheses are only `hi`, a real F, and all-matrix paired-inverse `basisInv`. No Booleanity, source-height condition, rank filter on data, or ρ is involved. | ✓ |

**Orientation.** The law is λᵢ = ∏_{j<s} (2^{d−i}−2ʲ)/(2^d−2ʲ) with d = c+s. That matches the argument's kernel-frame form: the numerator is the kernel dimension d−i and the denominator the full dimension d. The left side is the uniform mean over `BinaryMatrix n c`; the right is over `BinaryMatrix n (c+s)`. Each carrier is normalized by its own size, which is the normalization of the unconditional append operator.

**Smoke data.** The `candidate.json` values agree with my hand checks. For example, (c,s,i) = (2,1,1) gives 3/7, and (1,2,1) gives 1/7 = (3/7)(2/6). These are bounded checks only.

**Guard i≤c+s.** It is essential and is kept. With s=0 and i>c, the left ratio is 0/0 = 0 while the empty product is 1. Above that bound, rank-i frequencies on width c+s do not exist, so callers do not lose anything real by the guard.

## 3. Findings

| ID | Sev. | Declaration | Disposition and action |
|---|---|---|---|
| PD-1 | Verified | All 10 declarations | No action. |
| PD-2 | Low (stale text) | Module docstring "Uncompiled successor candidate" | Contradicted by the native receipt. Fix in the next revision; captured bytes stay immutable. |
| PD-3 | Info (non-claim) | `append_rank_projection_energy_eq_product` | Not consumed. The material RHS still uses 2^{−i(s−1)}+3·2^{i−n}, so this law does not tighten any material bound and should not be presented as doing so. |
| PD-4 | Medium, carried (X3/C105-05/NC105-3), narrowed | Manuscript operator route | The ratio→product step is now native. Still argument-level only: Φχ_Y = λᵢχ_Y with independent unrestricted B and full-row-rank C, GL completion and the uniform marginals, the invariant-first adjoint, the packaged ⟨T Pᵢ F, T Pⱼ F⟩ = δᵢⱼλᵢ‖Pᵢ F‖², and complex generality. |
| PD-5 | Info | `candidate.json` lists pre-repair source FD14D19B…/7058 bytes, `native_verified: false` | A historical Full106 artifact. The compiled bytes are 39E80A82…/7056. The two-byte "prod_div_distrib arity only" diff is not supplied, so it stands at receipt tier. |
| PD-6 | Info | Private `frame_pos` duplicates `ActualFiniteAppendExactImageEnergy.frameProduct_pos`; unnecessary `classical` | Hygiene only. |
| PD-7 | Info (evidence tier) | `GrassmannCounting.frameProduct` body | Not supplied in this packet. Its definition is inferred from consistent uses. Supply it for a fresh read during replay. |
| PD-8 | Info | +29 nodes / +5 boundaries | Not enumerated. Plausible. Enumerate during fresh-checkout replay. |
| PD-9 | Low/Medium, carried (FID-1/C105-03) | Lemma 4.7 / MZ24 A.13 crosswalk | The exact eigenvalue is a reconstruction, not a quotation of A.13, and the sourceHeightCutoff has no spectral role. Manuscript wording is still required. |
| R14 | **HIGH, carried** | Encoded reduction and runtime | **Bars overall GO.** The size of a parameter alone neither proves nor refutes this. |

The following remain carried and unchanged (Medium): numeric NO (`hfail` with a useful e, a, the scalar consumer, effective L₀); joint source, selection and global-table witnesses; joint arity; star and robust8S; pre-draw selection; the physical sampler; encoded reduction and learning; exact upstream transports; fresh source-object replay; inherited-warning certification; and the provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates. Legacy m-coupled and non-original exports still bind `hSpectral` (Low, C105-04).

## 4. Integration, re-confirmed against unchanged bytes

- **Bound statement.** The Full105 `…original_spectral_discharged` exports, with fixed window 4m ≤ k < 8m, and the `…at_dyadic_exponent_spectral_discharged` export, with caller dyadic k ≥ 4m, still hold under exactly these premises: `hsel` (floor `max(analyticSourceHeightFloor…, j+2)`), `1 ≤ samplerA`, `r < leafT+leafK`, `0 ≤ e`, `hfail(e)` on the same `selectedCoordinateLeafTable`, and `a > 0`. There is no HC46 premise and no Spectral47 premise.
- **Same objects throughout.** The same I, copies, U, A, C, T and f are used everywhere. `rows` stays independent of m. c+s = 2h ≤ 2J, with `hdim`, `hD` and `hsmall` derived. HC46 is discharged by `original_HC46_exact` at `hEven := hsplit`.
- **No substitution.** The append experiment is not replaced by uniform or rank-one noise, and the source and star families are not narrowed.
- **Upstream profiles.** The selected upstream profiles are not CMMSA bridges.
- **Still in force:** the actual SourceSize/HC46/dyadic and selected-leaf integration; the character pairing, tail-zero, orbit and counting lemmas; the weaker +3 contract; and exact normalization.
- **Prior conditional law.** The earlier real frame-ratio law keeps its explicit invariance, inverse, rank and carrier premises. The new product law supplies no source or sampler witness.

## 5. Safe conditional claim

This rests on pinned kernel and library trust, the Full107 receipts (260 standard profiles, seven stage exits of 0, 699 objects, terminated custody), the 8298-node trace with nothing unresolved, typed identities, and identity reuse.

For all n, c, s, i with i ≤ c+s, and every real F on `BinaryMatrix n (c+s)` invariant under all paired-inverse right actions:

1. G(c,i)/G(c+s,i) = G(c+s−i,s)/G(c+s,s).
2. That ratio equals ∏_{j<s} (2^{c+s−i}−2ʲ)/(2^{c+s}−2ʲ). This includes the genuine zero branch when i > c, and s = 0.
3. E_{M∈Mat(n,c)}[(A_s Pᵢ F)²] = ∏_{j<s}(…) · E_{W∈Mat(n,c+s)}[(Pᵢ F)²], for the unconditional append operator.

The Full105 conditional material bounds are unchanged.

**Not claimed:**
- the Φ eigen-relation, G/Φ, the adjoint, a packaged cross-level identity, or complex generality;
- source, sampler, selection or global-table witnesses;
- numeric NO;
- runtime, reduction or learning;
- upstream transports;
- replay or warning certification;
- novelty or priority (the classical append/Fourier/counting arguments are not new, and MZ24 A.13 states only the weaker bound);
- manuscript acceptance or overall GO.

## Remaining to-do

1. Prove natively the Φ kernel-frame eigen-relation with independent unrestricted B and full-row-rank C, the GL completion and uniform marginals, the invariant-first adjoint, and the packaged cross-level identity. Each needs a fresh review and trace.
2. Write the Lemma 4.7 / MZ24 A.13 crosswalk text: the exact eigenvalue as a reconstruction, the inert cutoff, and the unused guards and slack.
3. Supersede or wrap the legacy and non-original exports that still take `hSpectral`. Fix the stale headers (PD-2 and earlier ones) and the ambiguous flag labels.
4. Numeric NO: a certified scalar consumer (dyadic P ≥ max(4m, mT), Parseval side conditions, base/cutoff, effective L₀), then `hfail` at a useful e.
5. A joint witness for rows, copies, `TaggedGoodU`, A and `hsel`; source/star/robust8S; pre-draw selection and the global table; the physical sampler.
6. R14: an encoded or implicit reduction with a runtime proof; learning.
7. Upstream post-audit, then the exact CMMSA transports.
8. A fresh-checkout and source-object replay that recomputes every hash and DAG digest, enumerates the +29/+5 trace delta, supplies the Full106→107 diff, and freshly reads `GrassmannCounting`, `BinaryMatrixFourier`, `Diagonal` and `BigOperators/Field`.
9. Inherited-warning certification; disposition of the legacy hash field.
10. Final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates. Reconcile this report with the packet-1 report at the root.
