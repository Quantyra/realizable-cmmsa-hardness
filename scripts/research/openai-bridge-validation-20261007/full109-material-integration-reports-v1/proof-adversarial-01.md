# Full109 proof-adversarial review, packet 1 of 2: `ActualAppendProductCrossLevelIdentity` and the Full348/Full261/Focused93 integration

The cross-level Gram theorem is sound and native. I found no defect in its soundness, orientation, quantifiers, normalization, guards or edge cases. It is conditionally accepted at the theorem level only. This verdict covers packet 1; integration acceptance also needs the packet-2 report from this lens. Overall GO is not issued, because R14 (HIGH) and the other full-scope gates are still open.

**Method.** I used no tools, made no writes and ran no Lean, Lake or subagents. Every hash check below is a string comparison of values in the packet. Compile results, axiom profiles, trace and custody come from the qualified receipts.

## Verdicts

| Scope | Verdict |
|---|---|
| **Soundness of the two fresh bodies** (`ActualAppendProductCrossLevelIdentity.lean`, its Checks file) | **Sound.** No defect found. |
| **Native translation** | **Closed for the stated theorem.** It is the real, same-function cross-level Gram identity for the actual unconditional append operator, in exact if-then-else form, with a standard profile {propext, Classical.choice, Quot.sound}. |
| **Conditional integration** (SourceSize, HC46, dyadic, selected leaf, material callers) | **GO-WITH-NOTES, packet 1 only.** No HIGH is open in this scope. The material exports are byte-identical and unchanged. The new theorem is a root and no material export consumes it. |
| **Overall readiness** | **Not GO.** R14 (HIGH) is open, along with the numeric-NO, witness, source, upstream, replay, warning, provider and manuscript gates. |
| **Manuscript, novelty, priority** | No verdict and no acceptance. |

## 1. Coverage

| Body set | Status |
|---|---|
| `ActualAppendProductCrossLevelIdentity.lean` (source BB738BC9…CE90) | **Read line by line**: one theorem, the whole proof. |
| `ActualAppendProductCrossLevelIdentityChecks.lean` (113B8DDB…0739) | **Read in full.** It contains only `#check` and `#print axioms`, so it is log output, not evidence. |
| Interfaces in packet 1 re-derived for this review | `ActualAppendFourierCrossLevelOrthogonality` (the whole file, including `uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero`, `appendAverage_character`, `appendAverage_rankProjection_sum`, `uniformMean_sum`, `uniformMean_const_mul`). `ActualFiniteAppendSpectral47` (energy expansion, character pair). `ExactInhabitant`. `FrameProductRatio`. `PerImageEnergy`. `ImageWeighted`. `ImageOrbitFourier`. Legacy `AnalyticMoment`, which consumes the orthogonality via `appendHighLevel_energy_eq_sum`. `SourceSize AppendMoment`. `HC46OriginalApplication`. `RankImageRightBasisInvariance`. `FiniteMomentLpBounds`. Mathlib `ToLin` and `Rank`. |
| Other packet-1 parent bodies (Complexitylib, tagged/star/Cmmsa, sampler, covering, the `Nat`/`GroupWithZero`/`BigOperators` externals) | Present and byte-identical. Their semantic credit is reused per lens from the 45 preserved reports. **I did not reread them fresh.** |
| **Not in packet 1** | `ActualFiniteFrameProductDuality.lean`, which holds the diagonal dependency `append_rank_projection_energy_eq_product`. Also `ActualFiniteAppendExactImageEnergy.lean`, `BinaryMatrixFourier`, `GrassmannCounting`, and the declaration of `ite_eq_left`/`ite_eq_right`. For these I rely on identity reuse of the Full105/Full107 reviews; they are presumably in packet 2. |

**Skipped required fresh bodies: none.** I make no claim of a fresh reread of all 348 bodies. Packet 2 is outstanding for this lens.

## 2. Declaration audit: `append_rank_cross_level_gram_eq_product`

**Hypotheses**
- Natural numbers `n c s i j`.
- `hi : i ≤ c + s`.
- An arbitrary real `F : BinaryMatrix n (c+s) → ℝ`.
- `basisInv`: right invariance under paired inverses for every matrix M and every pair U, V with `U*V = 1` and `V*U = 1`. Deficient matrices are included.
- No Booleanity, source height, rank conditioning of sampled data, or bound on `j`.

**Conclusion**
- The left side is `uniformMean` over `Mat(n,c)` of `appendAverage(P_i F) · appendAverage(P_j F)`. That is one fixed F and the actual unconditional append operator: a uniform base and a uniform appended block.
- The right side is `if i = j then (∏_{k<s} (2^{c+s−i} − 2^k)/(2^{c+s} − 2^k)) · uniformMean_{Mat(n,c+s)} (P_i F)^2 else 0`.
- Each carrier is averaged over its own normalized mean. The exact if-then-else form is kept; the theorem is not weakened to an inequality.

**Diagonal branch**
- `subst j` replaces j with i, so the product is indexed by the guarded `i`.
- `rw [ite_eq_left rfl]` selects the product branch.
- `simpa only [pow_two]` rewrites `x^2` as `x*x` on both sides. This touches only literal squares. The powers `(2:ℝ)^(c+s−i)` and `(2:ℝ)^k` have no exponent 2, so they are unaffected.
- The branch then closes with Full107's `append_rank_projection_energy_eq_product hi F basisInv`, which is native and was reviewed by three lenses.

**Off-diagonal branch**
- `rw [ite_eq_right hij]` selects the zero branch.
- `exact uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero hij F`. I re-derived that theorem in this packet. It needs only `i ≠ j` and the same F, with no invariance or rank guard. Its two Fourier expansions over rank-i and rank-j frequencies have disjoint supports. `appendAverage_character_mul_eq_zero` holds because distinct ranks imply distinct frequencies. In the case where both tail blocks vanish, the head blocks differ, and `character_orthogonality` gives zero.
- `basisInv` and `hi` are unused in this branch. They are theorem binders, so there is no linter issue.

**Alias repair**
- The receipt says the only change from Full108 is that the deprecated `if_pos`/`if_neg` were replaced by `ite_eq_left`/`ite_eq_right`, with headers unchanged.
- Usage is consistent with the forms `ite_eq_left (h : c) : ite c a b = a` and `ite_eq_right (h : ¬c) : ite c a b = b`, which Complexitylib already uses (`Cheeger`, `FamilyFin`).
- The Full108 bytes (old B3F1C4F5…) were not supplied, so the "exact two-alias replacement" claim stays at receipt tier.
- I see no `set_option linter` and no suppression of any kind. That fits zero owned warnings and no baseline expansion; I did not independently verify the warning baseline.

**Edge cases**

| Case | Result |
|---|---|
| `c < i ≤ c+s` | The real factor at `k = c+s−i < s` is (x − x)/y = 0, so the product is 0. The later factors are negative reals, but the product is still exactly 0. This agrees with the zero retained count. |
| `s = 0` | `hi` forces `i ≤ c`. The empty product is 1, so post-append energy equals full energy. |
| `i = 0` | Every factor is 1, so the mean energy is preserved. |
| `n = 0` or zero widths | Singleton carriers, and only rank 0 exists. Consistent through the Full105/Full107 laws. |
| Empty rank support | Both sides are 0. |
| `j` with no bound (including `j > c+s`) | Covered by the off-diagonal branch. P_j F = 0 anyway. |
| Real denominators | `2^{c+s} − 2^k > 0` for every `k < s ≤ c+s`. |

## 3. Custody and bookkeeping

- **Typed identities.**
  - Main file: source BB738BC9…CE90 matches the header, `derivation.json` new_sha256, and the typed record. Object 5E713CCE…3AFD matches the legacy field.
  - Checks file: source 113B8DDB… matches; object 7E4E799D… matches.
  - No source hash equals any object hash.
- **Counts.**
  - Roots 260 + 1 = 261; focused 92 + 1 = 93; sources 346 + 2 = 348.
  - Nodes 8298 → 8299 (+1): exactly the root, with no auxiliaries.
  - External boundaries unchanged at 2767. That is consistent with `ite_eq_left`, `ite_eq_right` and `pow_two` already being reached. It is plausible but not enumerated.
- **Flags.**
  - Native-phase flags such as `material_body_review_complete: false` and `consumption_trace_complete: false` are historical.
  - `source_selection_complete: false`, `accepted: false` and `full_goal_complete: false` are current.
  - The relation of `cache_objects_unchanged: 566` to the actual object count is still unreconciled (carried).

## 4. Integration under the exact prior hypotheses

- **Material exports unchanged.** The SourceSize/HC46/dyadic/selected-leaf bodies are byte-identical. These all carry over:
  - independent `rows` and leaf arity `m`;
  - one `Tc` serving `hfail`, the PR premise and the moment;
  - `c+s = 2h ≤ 2J`, with `hdim`, `hD` and `hsmall` derived;
  - `original_HC46_exact` applied at `hEven := hsplit`;
  - the Full105 spectral discharge, `(spectral47_contract_iff _).mp (spectral47_exact_contract_inhabitant _)`;
  - the fixed window `4m ≤ k < 8m`, or a caller-chosen dyadic `k ≥ 4m`;
  - `hsel`, `hA`, `hrd`, `he`, `hfail` and `ha` retained.
- **Nothing substituted.** No uniform or rank-one surrogate, no narrowed source or star family.
- **Not consumed.** The new identity feeds no material export. `selected_actual_analytic_rhs` still uses `2^{−i(s−1)} + 3·2^{i−n}`, so nothing is tightened.
- **Relation to existing lemmas.** The off-diagonal half was already consumed through `appendHighLevel_energy_eq_sum`. Combined with the new diagonal law, it would give an exact high-energy formula, but no theorem packages that.

## 5. Findings

| ID | Severity | Item | Disposition |
|---|---|---|---|
| X109-1 | Verified | `append_rank_cross_level_gram_eq_product` | Sound and native. Conditional theorem-level acceptance. |
| X109-2 | Info | `hi` is also required on the off-diagonal | The Full90 orthogonality covers `i > c+s` directly. On the diagonal with `i > c+s`, both sides are 0 anyway because P_i F ≡ 0, so the guard could be dropped, but keeping it is sound. No action required. |
| X109-3 | Low (stale) | Header says "has not been compiled" | Contradicted by the receipt. Fix in the next revision; leave the immutable bytes. |
| X109-4 | Info (evidence tier) | `FrameProductDuality`, `ExactImageEnergy`, `BinaryMatrixFourier`, `GrassmannCounting`, `ite_eq_*` bodies are not in packet 1 | Identity reuse only until packet 2 is reviewed. |
| X109-5 | Info (custody) | The Full108 diff and old bytes are not supplied | The alias-only claim is receipt tier. |
| X109-6 | Medium (non-claim, carried) | Scope limits | Not covered: the G/Φ completion and marginals, independent B/C sampling, the pointwise Φ eigenrelation, the restricted adjoint, the two-function Gram identity, and the complex case. This theorem uses none of them. |
| Carried | Low/Medium | Lemma 4.7 / A.13 crosswalk; inert cutoff; F1-r legacy `hSpectral` exports; stale banners; flag labels; numeric NO; joint witnesses; upstream transports; replay; inherited-warning certification | Open. |
| **R14** | **HIGH** | Encoded reduction, runtime and learning | Open. **Bars overall GO.** |

## 6. Safe conditional claim

This rests on pinned kernel and Init/Mathlib/Batteries trust, the 261 standard profiles, seven stage exits of 0, the qualified 8299-node trace with 0 unresolved, the typed identities, and identity reuse of the 346 parent bodies and 8298 dependency nodes.

> For all n, c, s, i, j with i ≤ c+s, and every real F invariant under paired-inverse right actions:
> E_M[A(P_iF)·A(P_jF)] = [i = j] · ∏_{k<s} (2^{c+s−i} − 2^k)/(2^{c+s} − 2^k) · E_W[(P_iF)²].

The Full105 material bounds hold unchanged under their stated premises.

**Not claimed:** G/Φ, the eigenrelation, the adjoint, two-function or complex versions, any source/selection/global-table/star/robust8S/pre-draw/sampler witness, encoded reduction, runtime or learning, numeric NO, upstream transports, fresh replay, inherited-warning certification, the provider/novelty/citation/manuscript gates, or overall GO.

## Remaining to-do

1. Packet-2 review for this lens, covering the `FrameProductDuality` and `ExactImageEnergy` bodies, then root reconciliation across both packets and all three lenses.
2. Supply the Full108 → Full109 diff and the old bytes so the alias-only repair can be confirmed.
3. Native G/Φ completion and marginals, the Φ eigenrelation with independent B and C, the invariant-first adjoint, and two-function and complex extensions. Each needs independent review.
4. Decide whether to tighten the material RHS with the exact high-energy law, or state explicitly that the looser factor is kept.
5. The Lemma 4.7 / MZ24 A.13 crosswalk, including reconstruction wording and the inert cutoff.
6. Supersede or wrap the legacy `hSpectral` exports (F1-r). Fix the stale headers (X109-3) and the flag labels.
7. Numeric NO: a certified scalar consumer, `hfail` at a useful e, `base`/`cutoff`, and an effective L₀.
8. Joint witnesses for source, selection, global table, star/robust8S, pre-draw, and the physical sampler.
9. R14: an encoded or implicit reduction with a runtime proof; learning.
10. Upstream post-audit, then the exact CMMSA transports.
11. Fresh-checkout source and object replay with every hash and DAG digest recomputed, including enumeration of the node and boundary deltas; reconcile 566 against the actual object count; inherited-warning certification.
12. Final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates.
