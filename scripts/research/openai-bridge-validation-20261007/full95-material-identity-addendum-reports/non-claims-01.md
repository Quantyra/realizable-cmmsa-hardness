# Full95 non-claims review: identity addendum (H-1 / H1)

## Verdicts

| Scope | Verdict |
|---|---|
| **H-1 (proof-adversarial) / H1 (complexity)** | **Resolved. This is a category mismatch, not a custody defect.** It is now a Low bookkeeping item: the native report's field is keyed by the wrong path. |
| **Native and material conditional integration** (the 4 new bodies, read against the actual material lane) | **GO-WITH-NOTES.** No HIGH finding is unresolved in this scope. The conditional material verdicts in all three original reports now stand (see §5). |
| **Unconditional material readiness** | **NO.** Spectral47, numeric NO and a useful `e`, and joint source and selection witnesses are all still open. |
| **Overall full-goal GO, theorem readiness, manuscript readiness** | **Not issued.** R14 is still HIGH on the reduction and runtime gate. No novelty, priority or publication acceptance is given. |

**Method.** I used no tools, wrote nothing, and ran no Lean, Lake or subagents. I did not recompute any SHA-256, including the reconciliation's own `CB97732C…`.

Everything below is a string-level comparison of the hashes and labels you supplied, plus a re-reading of the source text. I treated the reconciliation as an author record, not as a certificate. Wherever a conclusion still depends on receipts, I say so.

## 1. Independent resolution of H-1

### 1.1 What H-1 actually compared

H-1 compared two things:
- the SHA in each supplied body's header, which is a hash of the `.lean` source;
- the native report's `added_object_hashes`.

The native report keys `added_object_hashes` by `lean/…/*.lean` paths. If its values are object hashes, then H-1 compared a source hash with a binary hash, both labelled with the source path. In that case the two values are never expected to be equal.

### 1.2 Source category: each `.lean` SHA against the body headers

| Module | Body header SHA | Mapping `source_sha256` | Match |
|---|---|---|---|
| SourceSizeAppendMoment | D4B86B56…5817 | D4B86B56…5817 | ✓ |
| SourceSizeAnalyticMoment | 03FB0A5D…D3D1 | 03FB0A5D…D3D1 | ✓ |
| SourceSizeOriginalApplication | 22DE415F…6C08 | 22DE415F…6C08 | ✓ |
| ManuscriptDyadicMoment | AF3E380A…A705 | AF3E380A…A705 | ✓ |

I checked each match on the full 64 hex characters, as far as the supplied strings allow.

The mapping also records that each source SHA matches the native source-before and source-after seals and the capture manifest. I cannot see the contents of `source-before.json`, so that link rests on receipts. Two things I can check from the strings:
- `source-before.json` and `source-after.json` have the same member pin (`AD79C9BA…D9DD`). That means the source seal did not change across the native build, which is consistent with "no normalization or source repair."
- The input archive pin `4BC7F2B3…A441` is the same Full95 input that the spectral-orbit note binds independently.

### 1.3 Object category: each `.olean` SHA against the qualified report

| Module | Mapping `compiled_object_sha256` (`.olean`) | Native report `added_object_hashes` (keyed by `.lean`) | Match |
|---|---|---|---|
| SourceSizeAppendMoment | 6E8EA03C…341D | 6E8EA03C…341D | ✓ |
| SourceSizeAnalyticMoment | B472BC2E…6EB6 | B472BC2E…6EB6 | ✓ |
| SourceSizeOriginalApplication | 3268034A…E7D9 | 3268034A…E7D9 | ✓ |
| ManuscriptDyadicMoment | C02909B6…9E1F | C02909B6…9E1F | ✓ |

**These are exactly the four pairs H-1 flagged.** Every "mismatched" value in the native report is the matching module's `.olean` hash. No value is unexplained, and no pair is crossed between modules.

The links from these hashes to the compiled-project and object-after inventories (`503C2D3D…`, `5AAA8156…`) also rest on receipts.

### 1.4 Custody pins cross-checked

| Pin | Reconciliation | Independent occurrence | Match |
|---|---|---|---|
| Native archive | E48640AC… | Native report `custody_sha256` | ✓ |
| Trace archive | 5267FD45… | Trace `custody.*_sha256` (all three) | ✓ |
| Qualified report | 6F164D49… | Header of the qualified native report | ✓ |

### 1.5 Corroboration that does not depend on the author's account

- **Declaration names.** The supplied bodies define exactly the eight new-module roots in `added_requested_axioms`. The ninth added root is the pre-existing Full90 export.
- **Trace membership.** The trace's project-module list contains all four new modules.
- **Repair markers.** The bodies contain the Full94 binder repair: `hHC rfl` in `selected_leaf_HC46_of_exact_PR`, and the `_hEven` / `_basisInv` / `_hc` … binders. The Full93 form `hHC (hEven := rfl)` was the native failure, and the reviewed text does not have it. So these are post-repair bytes, consistent with what compiled.
- **The `rows` binder.** All seven SourceSize and Dyadic roots take `Instance N rows`, which matches the native flag `source_row_independence_native_verified`.

### 1.6 Disposition

| ID | Prior → now | Basis |
|---|---|---|
| H-1 / H1 | HIGH → **resolved (category mismatch)** | The native report keys `.olean` hashes under `.lean` paths. Each source SHA matches its own body header. Each object SHA matches its own `added_object_hashes` value. The source-before and source-after seals are identical. There is no evidence of CRLF/LF normalization, a different source version, or any repair. |
| I-1 (new) | **Low (bookkeeping)** | The field label is misleading. Future native reports should key object hashes by `.olean` path and carry the source SHA in the same entry. |
| I-2 (new) | Info (evidence tier) | The links from each source SHA to the before/after seals and the manifest, and from each object SHA to the inventories, are receipt-tier evidence. That is the same tier as the compile and axiom facts already accepted. I did not reproduce them. |

I did **not** require a source file and its compiled binary to share a hash.

**Self-correction.** My original non-claims report listed the four body SHAs but did not compare them with `added_object_hashes`. It therefore missed the apparent mismatch that the other two lenses flagged. Their HIGH rating was the right conservative call until this mapping arrived. My original report stays unchanged.

## 2. The 172 / 173 / 181 labels

- **172** is the frozen original set of requested axioms (`original_requested_axioms: 172`).
- **173** is Full90, which is 172 plus `ActualSelectedComplementHC46OriginalApplication.selected_actual_material_moment_bound_original`. The flag `original173_requests_preserved` refers to this set.
- **181** is Full95, which is 172 plus the 9 entries in `added_requested_axioms`. The first of those 9 is the Full90 export itself. The other 8 are new: 2 in AppendMoment, 2 in AnalyticMoment, 1 in SourceSizeOriginalApplication and 3 in Dyadic.
- So 9 roots were added since the original, and 8 since Full90. The counts are consistent, and complexity N5 / non-claims F7 are **closed as bookkeeping**.
- I did not hand-count the 181-entry `exact181-native` list. The focused-thirteen list is consistent: 2 A22/HC46 roots, 3 Full90 application roots, and the 8 new roots make 13.

## 3. Historical native-phase flags versus later receipts

| Flag | Recorded in | Status now |
|---|---|---|
| `material_body_review_complete: false` | Native report (before the trace) | Historical. Three independent reviews exist, and they were conditional only on H-1, which is now resolved. |
| `consumption_trace_complete: false` | Native report | Historical. The later trace qualifies structurally: 8069 of 8069 nodes are exact type-edge matches and 0 are unresolved in either graph. |
| `independent_body_review_complete: false` | Trace | Historical at the time the trace was recorded. The same point as the first row applies. |
| `source_selection_complete: false` | Trace | **Not converted.** No receipt establishes it, so it is not credited. |
| `reviewer_H1_disposition_pending: true` | Reconciliation | This report supplies the disposition. |
| `accepted: false`, `full_goal_complete: false`, `numeric_NO_proven: false` | Throughout | Unchanged and correct. |

No original report was rewritten, and none needs to be. A later receipt adds evidence; it does not change what earlier flags meant when they were recorded.

## 4. Body coverage for this addendum

- **The 4 new bodies were re-read in full.** I focused on identity: declaration names against the 9 added roots, the `rows` binder, the repair markers, and the stale banners.
  - The Dyadic header ("Uncompiled candidate") and the SourceSizeOriginalApplication block comment are stale, as finding F6 already recorded.
- **The other 63 supplied bodies were not re-read in this pass.** These are 40 prior project bodies and 23 Complexitylib bodies. My original immutable report inspected all 67 and skipped none. The reuse audit records identical bytes, configuration, and 7979 constant types and edges, so I carry that coverage forward. I spot-compared the old OriginalApplication and AnalyticMoment against the new parallel copies only to confirm that the new contracts are alpha-equivalent to the old ones.
- **The remaining 279 prior bodies are credited by identity reuse only.** They were not re-read.

## 5. The original reports' conditional verdicts

| Original report | Verdict before | After the H-1 resolution |
|---|---|---|
| Proof-adversarial | GO-WITH-NOTES, conditional on H-1; overall GO withheld (H-1, R14) | The conditional material verdict **stands**. Overall GO is still barred by R14. |
| Complexity | Mathematics GO-WITH-NOTES; overall NO-GO held **solely** on H1 | Its native/material integration verdict becomes GO-WITH-NOTES on its own stated terms. R14 still bars overall GO. |
| Non-claims (mine) | GO-WITH-NOTES; no HIGH in scope | Unchanged, and now also bound to the identity of the native bytes. |

These are my readings of the reports' own stated conditions. I am not overriding the other reviewers.

## 6. Remaining HIGH findings and their scope

- **R14 (HIGH) is on the encoded reduction and runtime gate, outside the material-statement scope.** `J = blocks samplerA h` is doubly exponential in `h`, and the explicit tables cannot be materialized at polynomial size.
  - How large a fixed parameter is, on its own, neither proves nor refutes a runtime bound.
  - The gate stays open until there is an encoded or implicit reduction with a proven cost model.
- **No HIGH remains in the native/material conditional scope.**

## 7. Safe conditional claim

This claim rests on:
- the pinned kernel and Init / Mathlib / Batteries trust;
- the qualified Full95 receipts: 181 standard profiles, 323 sources, 7 stage exits of 0, and the custody pins in §1.4;
- the typed source-to-object identity in §1, at receipt tier;
- identity reuse of the 319 prior bodies.

> **`ActualSelectedComplementSourceSizeOriginalApplication.selected_actual_material_moment_bound_original`.** Take any `I : Instance N rows` with `rows` independent of m, and any copies, U, A, C, T, f, `base` and `sourceHeightCutoff`. Suppose:
> - the selector at the caller's analytic floor returns m;
> - `1 ≤ samplerA`;
> - `r < c+s`;
> - `0 ≤ e`;
> - `hfail(e)` holds on the same coordinate leaf table `Tc`;
> - `Spectral47ExactContract` holds for that cutoff;
> - `a > 0`.
>
> Then there is a dyadic k with 4m ≤ k < 8m such that `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)`, and the center mass equals the exact Grassmann fraction.
>
> **The `…original_at_dyadic_exponent` variant** gives the same conclusion for every dyadic k ≥ 4m that the caller chooses, with no existential over k.
>
> In both, HC46 is discharged by `original_HC46_exact`, and `hdim`, `hD` and `hsmall` are derived inside the proof.

**Not claimed:**
- universal Spectral47, or its fidelity to manuscript 4.7;
- numeric NO, or a useful `e` or `a` (setting `e = 1` makes `hfail` trivial);
- joint source and selection witnesses for I, copies, U, A, `hsel` and `hfail`;
- an effective L₀;
- the source/star route, robust8S or `AllAmbientInverse`;
- the encoded reduction, runtime or learning (R14);
- upstream bridges;
- zero total warnings, or a fresh-checkout replay;
- novelty, citations, rendering or publication;
- unconditional theorem or manuscript acceptance.

## Remaining to-do

1. **Bookkeeping (I-1):** re-key `added_object_hashes` by `.olean` path and include the source SHA in each entry. Optionally, publish a member listing of `source-before.json` so the source-SHA link can be checked beyond receipt tier.
2. **Spectral47:** machine-prove the orbit argument for the actual append operator, or keep it as an explicit premise. Add `Iff.rfl` bridges between the old and SourceSize contract constants, and audit fidelity to manuscript 4.7.
3. **Scalar calibration:** a caller floor that enforces the ρ-faithful `r < c+s`; choices of T and P; a Parseval proof that ΣEᵢ ≤ 1; the finite-sum and scalar comparisons; instantiating `base` and `cutoff`; and an effective L₀.
4. **Numeric NO:** prove `hfail` at a useful `e` on NO instances, bound the high energies B, and compare 2·RHS against the actual weighted-selection threshold.
5. **Joint inhabitance:** exhibit I (with rows ≥ 1), padded copies, `TaggedGoodU` at J, A, and `hsel` together.
6. **Source/star:** tagged acceptance → ordinary density → a selected f, all on the trace; robust8S; discharging `kappa` and `hexpand`; and reconciling MZ's 1−η completeness.
7. **R14:** an encoded or implicit reduction handling the doubly exponential J, explicit expander tables, and the cost of `rotVal`.
8. **Upstream:** the independent seven-target post-audit, then the CMMSA bridges.
9. **Hygiene:** retire or mark the old m-coupled exports as superseded; remove stale banners (F6); dispose of linter suppression and in-library `#print axioms` output; replay from a fresh checkout.
10. **Manuscript:** fidelity (E1 exponents, constants, PR wording, the m/rows semantics), then novelty and citation review, BibTeX/PDF QA, and the final full-scope providers.
