# Full109 non-claims review, packet 2 of 2: `ActualAppendProductCrossLevelIdentity` and conditional material integration

**Short answer:** the two new files are sound, and the same-function real cross-level Gram identity is now a native theorem. Overall GO is not issued: R14 is still HIGH, the packet-1 report and the root reconciliation are still outstanding, and the manuscript, publication and source gates are open.

## Verdicts

| Scope | Verdict |
|---|---|
| **Soundness of the 2 new files** | **Sound.** I found no defect in soundness, quantifiers, orientation, normalization, case split or vacuity. |
| **Native translation** | **Done for exactly one statement.** The same-function real Gram identity for the actual unconditional append now exists as a native theorem: the product coefficient times the original energy when i = j, and zero otherwise. It has a standard axiom profile per the receipt. |
| **Not translated** | G/Φ completion and marginals, independent B/C sampling, the Φ eigen-relation, the restricted (invariant-first) adjoint, the two-function Gram law, and complex-valued versions. |
| **Conditional SourceSize/HC46/dyadic/selected-leaf integration** | **GO-WITH-NOTES, conditional, unchanged.** No HIGH finding in this scope. The new theorem is a root and no material export uses it. |
| **Overall readiness** | **No GO.** R14 (HIGH) is still open, and so are the numeric, source, runtime, upstream, certification, provider and publication gates. Per-lens integration also needs the packet-1 report and the root reconciliation. |
| **Manuscript, novelty, priority** | **No acceptance.** |

**How I reviewed.** I used no tools, made no writes, and ran no Lean, Lake or subagents. Every hash comparison is a string comparison of values in the packet. Compile results, axiom profiles, trace and custody come from the receipts. I read all 45 preserved reports and carry their findings forward unchanged except where noted.

## 1. Coverage

| Body set | Status |
|---|---|
| `ActualAppendProductCrossLevelIdentity.lean` (BB738BC9…CE90) | **Read in full: the one declaration, its whole proof, and both branches.** |
| `ActualAppendProductCrossLevelIdentityChecks.lean` (113B8DDB…0739) | **Read in full.** It contains only `#check` and `#print axioms`, which produce log output, not evidence. |
| Interfaces this proof uses | I re-checked `ActualFiniteFrameProductDuality.append_rank_projection_energy_eq_product` (Full107; its body is in this packet). I re-checked the shape of the off-diagonal lemma through its call in SourceSize `appendHighLevel_energy_eq_sum`, together with this file's kernel-accepted `exact`. |
| The other 49 supplied parent bodies (SourceSize/Dyadic/HC46 exports, the image-energy chain, the tagged/star/Cmmsa files, 13 Complexitylib files, 2 Mathlib files) | Present and unchanged. I inspected them at the integration interfaces; their semantic credit is inherited from the prior reviews by identity. |
| Not in this packet | `ActualAppendFourierCrossLevelOrthogonality` (presumably in packet 1), `BinaryMatrixFourier`, and `GrassmannCounting`. For these I rely on identity reuse plus the type of the kernel-accepted call. |

- **Packet size.** This packet has 51 files. Two fresh bodies are shared with packet 1, giving 51 + 51 − 2 = 100, which matches the stated union.
- **Skipped required fresh bodies: none.**
- **No fresh reread claimed.** I am not claiming to have freshly reread all 348 bodies.

## 2. Declaration audit: `append_rank_cross_level_gram_eq_product`

**Hypotheses**
- Implicit naturals n, c, s, i, j, with `hi : i ≤ c + s`.
- An arbitrary real `F : BinaryMatrix n (c+s) → Real`.
- `basisInv`, which quantifies over every M and every paired inverse pair (U·V = 1 and V·U = 1). Deficient and zero matrices are included.
- There is **no j bound**, no Booleanity assumption, no rank filter on sampled data, and no source-height, ρ or parity premise.

**Left-hand side**
- `uniformMean` over `BinaryMatrix n c` of `appendAverage (P_i F) · appendAverage (P_j F)`.
- `appendAverage` is the original unconditional average over all n×s matrices B. One fixed F appears in both factors.

**Right-hand side**
- When i = j: `∏_{k<s} (2^{c+s−i} − 2^k)/(2^{c+s} − 2^k)` times `uniformMean` over `BinaryMatrix n (c+s)` of `(P_i F)²`. Each carrier uses its own normalized mean.
- Otherwise: 0.
- The conclusion is exactly this if-then-else. It is not weakened to an inequality and the input carrier is not changed.

**Diagonal branch**
- `subst j` eliminates j in favor of i, and `ite_eq_left rfl` selects the true branch.
- `simpa only [pow_two]` then turns `x^2` into `x*x` on both the goal and the Full107 law. That only matches the literal exponent 2, so the `2^(c+s−i)` and `2^k` factors are untouched.
- This consumes the native, three-lens-reviewed exact product-energy law with no extra premise.

**Off-diagonal branch**
- `ite_eq_right hij` selects the false branch.
- `exact uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero hij F` is the Full90 actual-append Fourier rank orthogonality.
- It needs neither `basisInv` nor a j bound. `¬ i = j` is definitionally `i ≠ j`.

**Edge cases**

| Case | Result |
|---|---|
| c < i ≤ c+s | Genuine zero factor at k = c+s−i < s, so 0 = 0. Real factors with larger k may be negative, but the product is exactly 0. |
| s = 0 | `hi` forces i ≤ c, the product is empty (= 1), and the energy is preserved. |
| i = 0 | Every factor is d/d = 1. |
| n = 0, zero widths | Singleton carriers. Only rank 0 has support; every other rank has an empty support. |
| i > n | Both energies are 0. |
| j > c+s, i ≠ j | Allowed. `P_j F = 0`, so the product is 0, consistent with the orthogonality lemma. |

**Info.** `hi` is retained even in the off-diagonal branch. It also costs nothing on the diagonal: if i > c+s there are no rank-i frequencies, so `P_i F = 0` and both sides vanish. The guard is conservative and excludes nothing real. The only practical constraint is that a caller with i > c+s and j ≤ c+s must swap the arguments, which the commutativity of multiplication allows.

**Warning repair (D-1, Low).** The file uses `ite_eq_left` and `ite_eq_right` where the derivation reports that deprecated `if_pos`/`if_neg` aliases were replaced, with headers unchanged.
- What I could check: the file contains no `set_option linter…`, and the receipt reports zero owned warnings and zero inherited-regression headers.
- What I could not check: the Full108 bytes (B3F1C4F5…) were not supplied, so I cannot confirm "only the aliases changed". The same applies to the claim that the warning baseline was not expanded. Both stand at receipt tier.

**Stale docstring (D-2, Low).** The file says "This successor candidate has not been compiled", which the native receipt contradicts. Fix it in the next revision; the immutable bytes stay as they are.

## 3. Custody and bookkeeping

**Typed identities** (source and object categories never cross-compared):

| File | Source SHA | Object SHA |
|---|---|---|
| Main | BB738BC9 = header = derivation `new_sha256` | 5E713CCE = legacy field |
| Checks | 113B8DDB = header | 7E4E799D = legacy field |
| `FrameProductDuality` (prior) | 39E80A82 (unchanged) | 6A0ADC71 (unchanged) |
| `ExactImageEnergy` (prior) | F3E06B03 (unchanged) | 76B3ED6A (unchanged) |
| SourceSize/Dyadic (prior) | unchanged | unchanged |

**Counts**
- Roots: 260 + 1 = 261. Focused set: 92 + 1 = 93. Sources: 346 + 2 = 348.
- Nodes: 8298 + 1 = 8299, with 8299 exact type-edge matches and 0 unresolved.
- External boundaries stay at 2767. That implies `ite_eq_left`, `ite_eq_right` and `pow_two` were already reached elsewhere. This is plausible but not enumerated (Info).

**Flags**
- **Historical, from earlier phases:** `readiness.json` (`probe_executed: false`, `native_qualification_pending: true`), the native report's `material_body_review_complete: false` and `consumption_trace_complete: false`, and the label `cache_objects_unchanged: 566`.
- **Still current:** `accepted: false`, `coverage_accepted: false`, `source_selection_complete: false`, `independent_body_review_complete: false`, `full_goal_complete: false`, `numeric_NO_proven: false`, and `exact_manuscript_eigenvalue_and_G_Phi_laws_closed: false`.
- **Still ambiguous:** `universal_Spectral47_inhabitant_proven: false` sits next to `native_verified: true` (carried).

## 4. Integration

- **Material exports unchanged.** The SourceSize original, Dyadic original and spectral-discharged exports are byte-identical. These all carry forward:
  - independent `rows`;
  - one `Tc` serving `hfail`, the PR step and the moment;
  - derived `hdim`, `hD` and `hsmall`;
  - `original_HC46_exact`;
  - a caller-chosen dyadic k ≥ 4m;
  - the selector, failed-zoom, rank and positivity guards;
  - Spectral47 discharged through `spectral47_contract_iff`.
- **No substitutions.** There is no uniform or rank-one substitute, and the source/star family is not narrowed.
- **Material RHS not tightened.** `selected_actual_analytic_rhs` still uses the factor `2^{−i(s−1)} + 3·2^{i−n}`. The new identity is not consumed, so it supplies no source, selection, global-table, star, robust8S, pre-draw, sampler, encoded-reduction, runtime or learning witness.
- **What changed.** The "packaged cross-level identity" item (X3 / C105-05 / NC105-3 / PD-4 / D107-5 / NC107-4) is now closed **for the real same-function case only**. Before this, SourceSize `appendHighLevel_energy_eq_sum` composed the orthogonality inline.

## 5. Findings

| ID | Severity | Item | Disposition |
|---|---|---|---|
| X109-1 | Verified | `append_rank_cross_level_gram_eq_product` | Sound and native. No action. |
| X109-2 | Info | `hi` retained in the off-diagonal branch; unnecessary in both branches | Harmless; optionally drop or symmetrize later. |
| D-1 | Low (receipt tier) | Alias replacement, no linter suppression, no baseline expansion | Supply the Full108 → Full109 diff. |
| D-2 | Low | Stale "not been compiled" docstring | Fix in the next revision. |
| X109-3 | Info (identity tier) | Body of `ActualAppendFourierCrossLevelOrthogonality` not in this packet | Covered by the Full90 review and the kernel-checked call. Confirm in the packet-1 report. |
| X109-4 | Info | Trace grew by 1 node and 0 boundaries; not enumerated | Enumerate during replay. |
| X109-5 | Medium (non-claim, narrowed) | G/Φ, independent B/C, Φ eigen-relation, restricted adjoint, two-function law, complex form | Still argument-level only. Do not cite this theorem for them. |
| Carried | Medium | Lemma 4.7 / MZ24 A.13 crosswalk (exact λ is a reconstruction; inert cutoff; unused guards and `+3` slack); numeric NO (`hfail`, useful e, scalar consumer, effective L₀); joint source/selection/global-table/arity witnesses; star, robust8S, pre-draw, sampler, encoded reduction, learning; exact upstream transports and post-objects | Open. |
| Carried | Low | F1-r (legacy and hHC-parametric exports still spectral-conditional); stale banners; flag labels; legacy hash field; fresh source/object replay; inherited-warning certification | Open. |
| **R14** | **HIGH** | Encoded reduction and runtime | Open. **Bars overall GO.** |

## 6. Safe claim

This rests on pinned kernel and library trust, 261 standard profiles, seven stage exits of 0, the 8299-node trace with nothing unresolved, the typed identities, and identity reuse of 346 bodies.

For all n, c, s, i, j with i ≤ c+s, and every real F invariant under all paired-inverse right actions, the actual unconditional append satisfies:

**E_M[A(P_iF)·A(P_jF)] = [i = j] · ∏_{k<s}(2^{c+s−i} − 2^k)/(2^{c+s} − 2^k) · E_W[(P_iF)²]**

Here M is averaged over n×c matrices and W over n×(c+s) matrices, each with its own normalized mean. The Full105–107 conditional material bounds are unchanged.

**Not claimed:**
- G/Φ, the eigen-relation, the adjoint, the two-function law, or a complex version;
- a tightened material RHS;
- numeric NO, any witnesses, sampler, reduction, runtime or learning;
- upstream transports, replay, or warning certification;
- novelty or priority (this is a classical Fourier/counting reconstruction, and A.13 states only the weaker bound);
- manuscript acceptance or overall GO.

## Remaining to-do

1. Write the packet-1 report and do the root per-lens reconciliation across both packets.
2. Supply the Full108 → Full109 diff and baseline evidence (D-1). Fix the stale docstring (D-2).
3. Prove natively the GL completion and marginals, Φ with independent B/C, the Φ eigen-relation, the invariant-first adjoint, the two-function Gram law and the complex continuation. Alternatively, keep the manuscript limited to the energy and Gram laws.
4. Lemma 4.7 / MZ24 A.13 crosswalk and reconstruction wording. Decide whether to tighten the material RHS.
5. Supersede or wrap the spectral-conditional legacy exports (F1-r).
6. Numeric NO: a certified scalar consumer, `hfail` at a useful e, base and cutoff, and an effective L₀.
7. Joint source, selection, global-table and arity witnesses; star, robust8S and pre-draw; the physical sampler.
8. R14: an encoded or implicit reduction with a runtime proof; learning.
9. Exact upstream transports and post-objects.
10. Fresh-checkout source and object replay with all hashes and DAG digests recomputed, including enumeration of the +1 node. Read `GrassmannCounting`, `BinaryMatrixFourier` and `AppendFourierCrossLevelOrthogonality` fresh. Certify inherited warnings.
11. Final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates.
