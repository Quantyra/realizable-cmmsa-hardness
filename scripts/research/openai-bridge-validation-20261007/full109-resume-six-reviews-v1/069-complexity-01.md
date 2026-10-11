# Full109 complexity review, packet 1 of 2: `ActualAppendProductCrossLevelIdentity` and conditional material integration

The new cross-level Gram identity is sound, and its conditional integration is GO-WITH-NOTES. **Overall GO is not issued**, because R14 (HIGH, encoded reduction and runtime) is still open.

## Verdicts

| Scope | Verdict |
|---|---|
| **The two fresh bodies:** `ActualAppendProductCrossLevelIdentity.lean` (1 theorem) and its Checks file | **Sound.** I found no defect in soundness, orientation, quantifiers, normalization, carriers, edge cases or vacuity. The statement is the exact `if i = j then λᵢ·E[(PᵢF)²] else 0`. It is not weakened to an inequality and its input carrier is unchanged. |
| **Native translation** | **Closed for the exact real same-function cross-level Gram identity,** with a standard profile {propext, Classical.choice, Quot.sound}. **Still open:** the G/Φ completion and marginal laws, independent B/C sampling, the pointwise Φ eigenrelation, the restricted adjoint, two-function and complex forms. |
| **Conditional SourceSize/HC46/dyadic/selected-leaf integration** | **GO-WITH-NOTES.** No HIGH finding in this scope. The material bytes are unchanged. The new identity is a standalone root that no export consumes. |
| **Overall readiness** | **No GO.** R14 (HIGH, encoded reduction/runtime) is open. Numeric NO, witnesses, source/star/sampler, upstream, replay, warning certification and publication gates are also open. Nothing is accepted for the manuscript, and no novelty or priority is claimed. |

**Method.** I used no tools, writes, Lean/Lake runs or subagents. All hash comparisons are string comparisons of supplied values. Kernel, profile, trace and custody facts come from the receipts. The full per-lens verdict needs this report, the packet-2 complexity report and the root reconciliation.

## 1. Coverage

| Set | Status |
|---|---|
| `ActualAppendProductCrossLevelIdentity.lean` (source BB738BC9…CE90) | **Read line by line; the one declaration and full proof re-derived.** |
| `ActualAppendProductCrossLevelIdentityChecks.lean` (113B8DDB…0739) | **Read in full.** It contains only `#check` and `#print axioms`, so it produces info output, not evidence. |
| Dependency bodies in this packet that I re-derived fresh | `ActualAppendFourierCrossLevelOrthogonality`: the full off-diagonal chain (`appendAverage_character`, `appendAverage_character_mul_eq_zero`, `appendAverage_rankProjection_sum`, `uniformMean_sum`/`const_mul`, and the target lemma).<br>`ActualFiniteAppendSpectral47` (energy expansion).<br>`ActualFiniteAppendSpectral47ExactInhabitant` (binder order).<br>`ActualFiniteFrameProductRatio`, `…ImageWeighted`, `…PerImageEnergy`, `…ImageOrbitFourier`.<br>Init `Nat/Basic`: confirms `Nat.mul_sub_right_distrib` and `Nat.mul_sub_left_distrib` take no hypotheses, which supports Full107's truncation-safety claim.<br>Mathlib `ToLin`, `Rank`, `GroupWithZero/Units/Basic`, `BigOperators/Ring/Finset`. |
| The other 39 supplied parent, Complexitylib and Mathlib bodies | Present and checked at the interfaces only. Their semantic credit is inherited by identity from the 45 reports; I did not re-derive them. |
| **Not in this packet** | `ActualFiniteFrameProductDuality.lean`, which holds the diagonal dependency `append_rank_projection_energy_eq_product`. Also not here: `ActualFiniteAppendExactImageEnergy`, `GlobalImageEnergy`, the SourceSize/Dyadic/SpectralApplication export bodies, `GrassmannCounting`, `BinaryMatrixFourier`, and core `ite_eq_left`/`ite_eq_right`. I credit these from the three-lens Full107 review (whose statement it quotes), the kernel's acceptance of the `simpa` step, and packet 2. |

**Skipped required fresh bodies: none.** All 45 prior reports were read. Their count reconciles: 18 + 6 + 3 + 6 + 3 + 3 + 6 = 45.

## 2. Declaration audit: `append_rank_cross_level_gram_eq_product`

**Hypotheses.**
- Binders `{n c s i j}` and `hi : i ≤ c+s`.
- `F` is an arbitrary real function.
- `basisInv` ranges over **all** M, with paired U·V = 1 and V·U = 1. There is no rank, Booleanity, height, ρ, parity or source premise.
- There is **no j guard**.

**Carriers.**
- The left side is `uniformMean` over `BinaryMatrix n c` of the product of two `appendAverage`s. Each `appendAverage` is the unconditional uniform over `BinaryMatrix n s`, and the same F appears in both factors.
- The right side is `uniformMean` over `BinaryMatrix n (c+s)`.
- Each carrier is normalized by its own size, with no stray factor.

**Diagonal branch.**
- `subst j` replaces j by i, `ite_eq_left rfl` selects the then-branch, and `simpa only [pow_two]` turns `x^2` into `x*x` on both sides.
- The step consumes Full107's `append_rank_projection_energy_eq_product hi F basisInv` unchanged.
- `pow_two` matches only the literal exponent 2, so the `(2:ℝ)^(c+s−i)` factors are untouched. The bound variable `k` and Full107's `j` are α-equivalent.

**Off-diagonal branch.**
- `ite_eq_right hij` selects the else-branch, and the proof is the exact Full90 lemma with `hij : i ≠ j` and the same F.
- I re-derived that lemma. Expand both projections into rank-i and rank-j frequency sums. For each pair (Z, Z′), rank Z ≠ rank Z′ implies Z ≠ Z′. Then either a tail is nonzero (that factor is identically 0), or both tails are zero and the base frequencies satisfy Y ≠ Y′, so character orthogonality gives 0. No bound on j is used.

**Edge cases.**

| Case | Result |
|---|---|
| c < i ≤ c+s | Genuine zero factor at k = c+s−i < s, and the left energy is 0. Later real factors may be negative, but the product is still exactly 0. |
| s = 0 | `hi` forces i ≤ c. The product is empty (= 1) and Mat(n,0) is a singleton. |
| i = 0 | Each factor is x/x with x = 2^{c+s} − 2^k > 0. |
| n = 0, c = 0, zero widths | Inherited from Full105/107, where only rank 0 exists. |
| Empty rank support | Sums are 0 on both sides. |
| j > c+s, j ≠ i | `rankProjection j F ≡ 0`, since `rank_le_width` leaves the filter empty. The off-diagonal 0 holds with no guard. |

**Retained guard (Info).** `hi` is kept, as required. In this energy form it is technically removable: if i > c+s, then `rankProjection i F ≡ 0` and both sides are 0. No action is needed; the point only matters for future simplification.

**Repair claim.**
- No `set_option linter…` appears; only `autoImplicit false` is set.
- The receipt reports 0 owned warnings and 0 inherited-regression warnings across all seven stages.
- `derivation.json` records an exact two-alias replacement with unchanged headers (B3F1C4F5 → BB738BC9). The Full108 bytes were not supplied, so I hold the diff at receipt tier.

## 3. Custody and bookkeeping

- **Source and object hashes.** Source BB738BC9…CE90 matches the header, `added_source_object_identities` and `derivation.json`. Its object is 5E713CCE…3AFD, which matches the legacy field. The Checks file pairs source 113B8DDB with object 7E4E799D. No source hash equals an object hash.
- **Counts:**
  - 260 + 1 = 261 roots; 92 + 1 = 93 focused; 346 + 2 = 348 sources.
  - 8298 + 1 = 8299 nodes with exact type-edge matches.
  - External boundaries stay at 2767, and 0 entries are unresolved in both graphs.
  - The one-node growth fits a single root whose dependencies are all prior nodes. That is an inference; the delta was not enumerated.
- **Parent settlement.** The settlement hash 0BF97A64 equals the Full107 root reconciliation.
- **Historical flags.** `readiness.json` (`probe_executed: false`), and `material_body_review_complete`/`consumption_trace_complete: false` in the native report, are historical. The qualification summary supersedes them structurally. `source_selection_complete`, `independent_body_review_complete` and `accepted: false` remain current.

## 4. Integration (unchanged bytes, exact prior hypotheses)

- **No consumer.** No SourceSize, HC46, dyadic, spectral-discharged or selected-leaf export consumes the new identity.
- **Prior bounds unchanged.** The Full105 `…original_spectral_discharged` bounds are unchanged: fixed window 4m ≤ k < 8m, or any caller-chosen dyadic k ≥ 4m. They hold with neither an HC46 nor a Spectral47 premise, under `hsel`, `1 ≤ samplerA`, `r < leafT + leafK`, `0 ≤ e`, `hfail(e)` on the same `selectedCoordinateLeafTable`, and `a > 0`.
- **Shared structure unchanged.** `rows` remains independent of m, and the same I/copies/U/A/C/T/f are used. `hdim`, `hD` and `hsmall` remain derived. There is no uniform or rank-one surrogate and no narrowing of the source/star family.
- **RHS not tightened.** `selected_actual_analytic_rhs` still uses 2^{−i(s−1)} + 3·2^{i−n}. The selected-leaf high-energy path already uses the same Full90 orthogonality plus the per-level contract.

## 5. Findings

| ID | Severity | Declaration | Disposition and action |
|---|---|---|---|
| X109-01 | Verified | `append_rank_cross_level_gram_eq_product` | Exact same-function real Gram law. Diagonal is λᵢ·energy; off-diagonal is 0 with no j guard. |
| X109-02 | Info | the `hi` guard | Kept as required; removable in energy form. No action. |
| X109-03 | Low (stale) | Header says "has not been compiled" | Contradicted by the receipt. Fix in the next revision; the captured bytes are immutable. |
| X109-04 | Info (non-claim) | the theorem | Not consumed and does not tighten the material RHS. It does not establish G/Φ, marginals, independent sampling, the Φ eigenrelation, the restricted adjoint, or two-function/complex forms (polarization does not give the two-function off-diagonal law). |
| X109-05 | Info | Checks harness | `#print axioms` output is log only. |
| X109-06 | Low (evidence tier) | `FrameProductDuality`, `ExactImageEnergy`, `GrassmannCounting`, `BinaryMatrixFourier` bodies; core `ite_eq_*`; Full108→109 diff | Not in this packet. Covered by packet 2 and replay. |
| X109-07 | Info | Reuse audit | Duplicate `accepted` key. The Full107 entries omit `native_exit`/`context_fit`, which are supplied instead by root reconciliation 0BF97A64. Hygiene only. |
| Carried | Low | F1-r legacy m-coupled exports that still take `hSpectral`; stale banners; legacy hash field; the unreconciled 566/699/… object count; inherited warnings | Open. |
| Carried | Medium | Numeric NO/`hfail`/e/scalar; joint source/selection/global-table witnesses; joint arity; star/robust8S; pre-draw draws; sampler; Lemma 4.7/MZ24 A.13 crosswalk; upstream transports | Open. |
| **R14** | **HIGH** | Encoded reduction/runtime/learning | Open. **Bars overall GO.** |

## 6. Safe conditional claim

This rests on pinned kernel and Init/Mathlib/Batteries trust, 261 standard profiles, seven stage exits of 0, the qualified 8299-node trace with no unresolved entries, typed identities, and identity reuse of 346 bodies and 8298 nodes.

For all n, c, s, i, j with i ≤ c+s, and every real F invariant under all paired-inverse right actions:

E_{M∈Mat(n,c)}[A_s(PᵢF)(M) · A_s(PⱼF)(M)] = **if i = j then** ∏_{k<s}(2^{c+s−i} − 2^k)/(2^{c+s} − 2^k) · E_{W∈Mat(n,c+s)}[(PᵢF)(W)²] **else** 0.

The Full105 conditional material bounds are unchanged.

**Not claimed:**
- G/Φ, marginals, independent sampling, the eigenrelation, the adjoint, or two-function/complex generality;
- witnesses, numeric NO, the encoded reduction, runtime or learning;
- upstream transports, replay, or warning certification;
- final provider, novelty, citation or manuscript gates;
- overall GO.

## Remaining to-do

1. Packet-2 complexity report, then root per-lens reconciliation.
2. Native G/Φ completion counts and uniform marginals, the Φ eigenrelation with independent unrestricted B and full-row-rank C, the invariant-first restricted adjoint, two-function and complex Gram forms. Each needs independent review.
3. Lemma 4.7/MZ24 A.13 crosswalk: the exact λᵢ presented as a reconstruction, the inert cutoff, the unused guards and slack.
4. Decide whether a material consumer should use λᵢ or keep the looser factor explicitly. Supersede or wrap the F1-r legacy exports.
5. Numeric NO: certified scalar consumer, `hfail` at a useful e, base/cutoff, and an effective L₀.
6. Joint I/copies/U/A/`hsel` witness; source/star/robust8S; pre-draw global table; physical sampler.
7. R14: encoded/implicit reduction with a runtime proof; learning.
8. Exact upstream transports and post-object audit.
9. Fresh-checkout source/object replay recomputing all hashes and DAG digests, including enumeration of the +1 node and the Full108→109 diff. Certify inherited warnings and reconcile the object counts.
10. Hygiene: stale headers (X109-03), flags, legacy field, reuse-audit keys.
11. Final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates.
