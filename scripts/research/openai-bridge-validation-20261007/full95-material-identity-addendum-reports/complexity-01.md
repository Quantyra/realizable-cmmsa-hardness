# Full95 identity addendum: independent resolution of complexity H1 / proof H-1

## Verdicts

| Scope | Verdict |
|---|---|
| **H1 / H-1** | **Resolved. It was not a custody defect.** The original finding compared source-byte hashes with compiled-object hashes. These are two different kinds of artifact, so they were never expected to match (details below). What remains is a Low finding about how far the receipt can be trusted: the matching is consistent but I did not recompute it. |
| **Native and material conditional integration** (the 4 new bodies, read against the actual material route) | **GO-WITH-NOTES.** The original complexity verdict ("conditional on H1") now stands. |
| **The other two original Full95 reports** | **Proof-adversarial:** its GO-WITH-NOTES was conditional on H-1, and it now stands. **Non-claims:** it never raised the hash comparison, so its GO-WITH-NOTES stands unchanged. All three reports are preserved as written; this addendum adds to them and does not edit them. |
| **Overall full-goal GO** | **Not issued.** R14 is still open as a HIGH on the separate reduction/runtime gate (scope below). Spectral47, numeric NO, joint witnesses, source/star, the bridges and publication are also still open. |
| **Unconditional theorem or manuscript acceptance** | **None.** |

**Method.** I used no tools and made no writes. I did not run Lean or Lake, and I recomputed no hashes. Everything below is a cross-check between the artifacts you supplied. The contents of the archive members (`source-before.json`, `source-after.json`, `compiled-project-objects.json`, `object-after.json`, `capture-manifest.json`) were not supplied. I could see only their pinned hashes and the identity booleans the mapping claims for them.

## 1. H1: an independent comparison

### 1a. What H1 compared

The native report's `added_object_hashes` field is **keyed by `.lean` source paths but holds `.olean` object hashes**. Both original reports read the value under `…/X.lean` as if it were that source file's hash. That is a comparison across categories. A UTF-8 `.lean` file and its compiled `.olean` binary are different byte strings, so their hashes are never expected to be equal.

The mislabelled key is the immediate cause of H1. I record it as a new Low hygiene finding (ID-1 below).

### 1b. Source hashes, checked under each `.lean` path

| File | Header SHA in the review packet | Mapping `source_sha256` | Match |
|---|---|---|---|
| SourceSizeAppendMoment | D4B86B56…5817 | D4B86B56…5817 | ✓ |
| SourceSizeAnalyticMoment | 03FB0A5D…D3D1 | 03FB0A5D…D3D1 | ✓ |
| SourceSizeOriginalApplication | 22DE415F…6C08 | 22DE415F…6C08 | ✓ |
| ManuscriptDyadicMoment | AF3E380A…A705 | AF3E380A…A705 | ✓ |

- **Native source seals.** `source-before.json` and `source-after.json` have the same pinned hash (AD79C9BA…D9DD). So the source index did not change during the native run, and no repair or normalization happened inside the build. This agrees with `source_normalization_or_repair_performed: false` and `compiler_invoked: false`.
- **Capture manifest.** The mapping's `capture_manifest_sha256` equals its archive member pin (0D7BC8E8…1732).
- **What rests on attestation.** The claim that the D4B86B56… entries actually appear inside `source-before.json` and the capture manifest is the mapping's boolean `frozen_input_review_packet_and_native_before_after_source_identity: true`. I could not open those members.
- **Line endings.** If those booleans are true, the review-packet bytes are exactly the native bytes. That rules out CRLF/LF drift, which my original H1 named as a possible cause.
- **File sizes.** 11971, 66532, 6789 and 19470 bytes are plausible for the line counts and multibyte UTF-8 content I read. I did not count them.

### 1c. Object hashes, checked under each `.olean` path

| `.olean` path in the mapping | Mapping `compiled_object_sha256` | Qualified report `added_object_hashes` value (under the `.lean` key) | Match |
|---|---|---|---|
| …SourceSizeAppendMoment.olean | 6E8EA03C…341D | 6E8EA03C…341D | ✓ |
| …SourceSizeAnalyticMoment.olean | B472BC2E…6EB6 | B472BC2E…6EB6 | ✓ |
| …SourceSizeOriginalApplication.olean | 3268034A…E7D9 | 3268034A…E7D9 | ✓ |
| …ManuscriptDyadicMoment.olean | C02909B6…9E1F | C02909B6…9E1F | ✓ |

- **Report and custody pins.** The mapping's `qualified_report_sha256` (6F164D49…3DA) equals the header of the supplied qualified report. Native custody E48640AC… matches the report's `custody_sha256`, with the same short, repository and remote copies. Trace custody 5267FD45… matches the supplied trace.
- **Inventories.** `compiled-project-objects.json` (503C2D3D…) and `object-after.json` (5AAA8156…) are pinned. That the `.olean` hashes appear in them is again attested by the mapping's booleans, not seen by me.

### 1d. Corroboration from the bodies (my own reading, not taken from the mapping)

- **Root names.** All 8 new requested roots named in the qualified report are declared, with exactly those fully qualified names, in the reviewed bytes:
  - SourceSizeAppendMoment: `selected_actual_append_moment`, `selected_actual_center_identity`.
  - SourceSizeAnalyticMoment: `selected_actual_source_dimension_bound`, `selected_actual_material_moment_bound`.
  - SourceSizeOriginalApplication: `selected_actual_material_moment_bound_original`.
  - ManuscriptDyadicMoment: the three `…_at_dyadic_exponent` roots.
- **Native flags against content.** The reviewed bytes contain what the native flags assert was compiled:
  - `Instance N rows` in every SourceSize root, matching `source_row_independence_native_verified`;
  - the positional `hHC rfl` together with the `_hEven`, `_basisInv` … binders, which is the Full94 repair of the Full93 binder-call failure;
  - the `hklt`-free dyadic consumer, matching `manuscript_dyadic_consumer_native_verified`.
- **What this shows and doesn't.** These checks are consistent with the mapping. They are not proof of byte identity.

### 1e. Disposition

| ID | Prior severity | Now | Evidence | Residual |
|---|---|---|---|---|
| H1 (complexity) / H-1 (proof) | HIGH (custody) | **Resolved as a non-defect: the comparison crossed artifact categories** | §1b–1d. Every pin I can see agrees across five independent artifacts. No pin contradicts another. | **ID-2, Low (scope of the receipt):** the presence of these hashes inside the member JSONs is attested, not seen. This is the same trust tier my original review already applied to every native fact (181 profiles, exit codes). It is cleared by recomputing from the custody tarball during fresh-checkout replay. |
| ID-1 (new) | — | **Low (hygiene)** | `added_object_hashes` is keyed by `.lean` paths | Future reports should key object hashes by `.olean` path, or emit typed `{source_path, source_sha, object_path, object_sha}` records. |

## 2. Labels: 172 / 173 / 181

- **172 (original):** the frozen pre-Full90 request set. The native report's `original_requested_axioms: 172` refers to this.
- **173 (Full90):** the 172 plus `ActualSelectedComplementHC46OriginalApplication.selected_actual_material_moment_bound_original`.
- **181 (Full95):**
  - 172 + 9: the report's `added_requested_axioms` lists the Full90 export plus 8 new roots;
  - equivalently, 173 + 8;
  - the mapping records `added_since_original 9` and `added_since_full90 8`.
- **Check:** the 8 new roots in the exact181 list are exactly the 8 SourceSize/Dyadic declarations in §1d. `original173_requests_preserved: true` refers to the Full90 set.

This **resolves my N5** (non-claims F7 is the same point). The labels are consistent once "original" is read as "frozen 172". I did not hand-count all 181 entries.

## 3. Historical flags versus later receipts

**Flags from the native phase, recorded before trace and review.** These are snapshots and are not rewritten:
- native report: `material_body_review_complete: false`, `consumption_trace_complete: false`, `accepted: false`;
- trace: `independent_body_review_complete: false`, `coverage_accepted: false`;
- reuse audit: `new_review_complete: false`;
- mapping: `reviewer_H1_disposition_pending: true`.

**What later records establish:**
- the qualified structural trace (8069/8069 exact type-edge matches, 0 unresolved in both graphs, all 4 new modules listed);
- the reuse identity audit (319 unchanged + 4 new = 323; 7979 shared constant types and edges unchanged);
- this disposition of H1.

**Flags that are still substantive, not merely historical:**
- `source_selection_complete: false` (acceptance → fixed f is unproved);
- `numeric_NO_proven: false`;
- `Spectral47_numeric_and_full_manuscript_gates_open: true`;
- `full_goal_complete: false`.

## 4. Body coverage for this reaffirmation

- **Re-inspected for this addendum:** all 4 new bodies, in full. I confirmed each against the content checks the mapping depends on, and against the call sites:
  - new-namespace `HC46ExactContract` and `Spectral47ExactContract` with underscored binders, and `hHC rfl`;
  - `rows` as an independent binder in every SourceSize theorem;
  - the material theorem calling `ActualSelectedComplementSourceSizeAppendMoment.selected_actual_append_moment`, not the old m-coupled one;
  - `original_HC46_exact` (typed at the old contract) accepted at the new contract's slot by definitional equality;
  - the dyadic proof with `hklt` deleted and all guards derived.

  Nothing in my original Full95 complexity mathematics changes.
- **Reused from my original Full95 pass**, which read all 67 supplied bodies in full; this packet supplies them unchanged:
  - the 5 critical prior bodies;
  - the 35 other prior project bodies;
  - the 23 Complexitylib bodies.

  I claim no new line-by-line re-reading of these for this addendum.
- **Not read: 279 prior bodies.** They are covered only by identity reuse. This is not a re-reading.

## 5. Remaining HIGHs and their exact scope

- **Material conditional scope:** none.
- **R14, HIGH, open on the reduction/runtime gate only.** No theorem shows that the encoded reduction runs in polynomial time, or that it avoids materializing objects indexed by J = `blocks samplerA (hBlock L m)` = 2^(2^(A·h²)). Following your instruction, J's size alone is **neither a runtime disproof nor a proof**. An implicit construction might avoid it. R14 is an unmet proof obligation, not a demonstrated defect. It blocks only the overall/full-goal GO, not the material conditional verdict.

## 6. Safe conditional claim

This rests on:
- pinned kernel and Init/Mathlib/Batteries trust;
- the Full95 qualified receipts: 181 standard profiles, 323 sources, seven stage exits of 0;
- the typed source-to-object mapping (cross-consistent, with the member contents attested);
- identity reuse of the 319 prior bodies.

> Assume `I : Instance N rows`, with `rows` unrelated to m, and any `copies`, `U : TaggedGoodU`, side complement `A`, fixed tagged tables `C` and `T`, functional `f`, `base` and `sourceHeightCutoff`. Suppose:
> - `selector(max(analyticSourceHeightFloor base cutoff j, j+2)) L = m`;
> - `1 ≤ samplerA`;
> - `r < c+s`;
> - `0 ≤ e`;
> - `hfail(e)` holds on the same coordinate leaf table;
> - `Spectral47ExactContract cutoff` holds;
> - `a > 0`.
>
> Then, with **no HC46 premise** (discharged by `original_HC46_exact`):
> - **SourceSize root:** there is a dyadic k with 4m ≤ k < 8m such that `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)`, and the matching center mass equals the exact Grassmann fraction.
> - **Dyadic root:** the same conclusion holds for every caller-chosen dyadic k ≥ 4m.
>
> The finite sampling guards (`hdim`, `hD`, `hsmall`) are derived inside the proofs. The reviewed source bytes are those identified with the compiled objects listed in §1c.

**Not claimed:**
- Spectral47 in general, or its fidelity to manuscript 4.7;
- a numeric NO bound, or a useful e or a;
- joint source/selection witnesses (I, copies, U, A, `hsel`, `hfail`), or an effective L₀;
- source/star/robust8S, or the link from acceptance to f;
- encoded reduction, runtime (R14) or learning, or expander explicitness;
- upstream or CMMSA bridges;
- zero total warnings, or a fresh checkout;
- novelty, citations or publication;
- acceptance of the theorem or the manuscript.

## 7. Remaining to-do

1. **ID-2:** during fresh-checkout replay, recompute the four source and four object hashes from custody tarball E48640AC…. Confirm them against the `source-before`, `source-after`, capture-manifest, `compiled-project-objects` and `object-after` members.
2. **ID-1:** re-key object hashes by `.olean` path, or emit typed pairs, in future native reports.
3. **Spectral47:** a Lean proof for the actual append operator (GL orbit, Fourier covariance, orbit counts, Parseval). Add `Iff.rfl` bridges between the duplicated contracts, and audit fidelity to manuscript 4.7.
4. **Scalar consumer:** certify it. Choose r, T and P; prove Parseval Σ E_i ≤ 1 and B ≤ 2^(−r(s−1)); instantiate `base` and `cutoff` (including h > 20000m³); give an effective L₀. Then prove `hfail` at a useful e on NO instances (numeric NO).
5. **Joint witness:** a joint-inhabitance witness for I (rows ≥ 1), padded copies, U, A, C, T and f at the selected m.
6. **Source/star:** acceptance → fixed f on the trace; `AllAmbientInverse`/robust8S; discharge `kappa`/`hexpand`; reconcile completeness 1 − η.
7. **R14:** an encoded reduction with a runtime proof, implicit if needed. Explicit expander tables, `rotVal` cost, and the relation between L and instance size. No runtime claim may rest on Complexitylib.
8. **Upstream:** post-audit of the seven-target receipt, then the CMMSA bridges.
9. **Hygiene:** retire or mark superseded the m-coupled old roots; remove stale banners ("Uncompiled candidate", "not compiled"); dispose of warnings, linter suppression and in-library `#print axioms` output.
10. **Release:** manuscript fidelity (E1 exponents, constants, PR wording, rows/m semantics); novelty, citation, BibTeX and PDF QA; the final full-scope providers.
