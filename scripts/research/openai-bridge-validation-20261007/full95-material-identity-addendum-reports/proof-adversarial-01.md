# Proof-adversarial addendum: Full95 source/object identity (H-1) and full-scope reaffirmation

## Verdicts

| Scope | Verdict |
|---|---|
| **H-1** (proof-adversarial) / **H1** (complexity) | **Not a custody defect.** The comparison set source-file hashes against hashes of different files. It is closed for the material scope, on the condition stated in §1. Downgraded to a Low labelling finding, H-1a. |
| **Native/material conditional integration** of the 4 new bodies and the 181-root scope | **GO-WITH-NOTES.** The conditional verdict in the original proof-adversarial report now stands. |
| **Overall full-goal GO** | **Not issued.** R14 is still an open HIGH on the reduction/runtime gate, and the other full-scope gates are still open. |
| **Unconditional material readiness** | **No.** |
| **Theorem or manuscript** | **No acceptance.** |

**How I reviewed.** I used no tools, wrote nothing, ran no Lean or Lake, and recomputed no hashes. Every hash comparison below is a character-by-character comparison of the 64-character strings supplied in the packet. I did not accept the author's explanation because other reports agreed with it; I re-derived the argument below.

## 1. Independent resolution of H-1

**The category argument.** A `.lean` source and its `.olean` object are different byte strings, so their SHA-256 values are expected to differ. The original H-1 compared each body header's source SHA with the native report's `added_object_hashes`. Read literally, that field holds object hashes. The comparison only looked like a defect because the report keys those object hashes by the **`.lean` source path**. That keying convention is the actual labelling problem.

**Checks I made against the supplied text:**

| Check | Result |
|---|---|
| Body-header source SHA vs mapping `source_sha256`, all 4 files (D4B86B56…5817, 03FB0A5D…D3D1, 22DE415F…6C08, AF3E380A…A705) | Exact match, all 4 |
| Native report `added_object_hashes` vs mapping `compiled_object_sha256`, all 4 (6E8EA03C…341D, B472BC2E…6EB6, 3268034A…E7D9, C02909B6…1E9F) | Exact match, all 4, each under the same file stem |
| Overlap between the set of source SHAs and the set of object SHAs | None. Each path has exactly one hash of each kind. |
| Native custody E48640AC…6EE2 | Same in the mapping and the qualified report |
| Qualified report SHA 6F164D49…3DA | Same in the mapping and the report header |
| Trace custody 5267FD45…8B13 | Same in the mapping and the trace |
| Input archive 4BC7F2B3…A441 | Same in the mapping and the spectral-orbit note |
| `source-before.json` vs `source-after.json` pins | Identical (AD79C9BA…D9DD). The sources did not change during the build. |
| Body content vs native success | The reviewed bodies contain the Full94 binder repair (`hHC rfl`, `_hEven`). Full93 failed natively on exactly that call, so these bytes are consistent with being the bytes that compiled. This is weak corroboration only. |

**What I could not check myself.** The contents of `source-before.json`, `source-after.json`, `capture-manifest.json`, `compiled-project-objects.json` and `object-after.json` were not supplied, only their pins. So I cannot see for myself that each source SHA sits under its `.lean` path in the before/after seals and the capture manifest, or that each object SHA sits under its `.olean` path in the compiled-project and object-after inventories. Those memberships are attested by the mapping's verified flags. That is the same receipt tier I already rely on for compile status, axiom profiles and the trace.

**Disposition.**
- **H-1 (HIGH, identity): closed**, conditional on the mapping receipt's membership flags.
- It becomes **H-1a, Low (receipt hygiene)**. The native report's `added_object_hashes` should be keyed by `.olean` path, or carry explicit `source_path` and `object_path` fields. Future receipts should do so.
- The reviewed text is bound to the compiled bytes on two assumptions:
  - the hex strings above are faithful to the receipts;
  - the displayed body text is faithful to its header SHA. This transcription assumption applies equally to every other reviewed body.
- No normalization or source repair is claimed or needed.

## 2. The 172 / 173 / 181 labels (reconciled; complexity N5 closed)

I counted the `exact181-native` root list by hand: **181 entries**. Entries 1–173 are the Full90 set:
- 170 HC46/A-chain roots;
- the three `HC46OriginalApplication` roots.

The Full90 export `HC46OriginalApplication.selected_actual_material_moment_bound_original` is entry 173. Entries 174–181 are the 8 new SourceSize and Dyadic roots.

The arithmetic is consistent both ways:
- **From the frozen original:** 172 = 173 minus the Full90 export, and 172 + 9 added = 181. The native report's "added" list of 9 starts with that export.
- **From Full90:** 173 + 8 = 181, with Full90's order preserved.

`focused-thirteen-consumer` has exactly 13 entries. The SourceSize `selected_leaf_*` wrappers are correctly absent, since they compile but are not roots.

## 3. Historical flags versus later receipts

| Flag | Where | Status now |
|---|---|---|
| `consumption_trace_complete: false` | Native report (before the trace) | Historical. Superseded in the structural sense by the later trace: 8069/8069 exact type edges, 0 unresolved in both graphs, all four new modules present. |
| `material_body_review_complete: false` | Native report | Historical for the review step. The three Full95 reports and this addendum now cover the bodies, but that is review, not acceptance. |
| `source_selection_complete: false` | Trace (later) | **Still current. Open.** |
| `independent_body_review_complete: false`, `coverage_accepted: false`, `accepted: false` | Trace / termination | Current. Not overridden by this addendum. |
| `new_review_complete: false`, `accepted: false` | Reuse audit | Current. |
| `numeric_NO_proven: false`, `Spectral47_numeric_and_full_manuscript_gates_open: true` | Native report | Current. Open. |

## 4. Body inspection and reuse coverage

**In this pass:**
- I re-read the **4 new bodies in full**: SourceSizeAppendMoment, SourceSizeAnalyticMoment, SourceSizeOriginalApplication, ManuscriptDyadicMoment.
- I re-checked these specific call interfaces:
  - `hsel` floor identity: `analyticSourceHeightFloor base cutoff` passed as `sourceHMin` reduces by beta to the selector floor.
  - `hdim`: c+s = 2h ≤ 2J follows from h ≤ h² < J.
  - `selected_actual_source_dimension_bound`.
  - The Dyadic guards: from 4m ≤ k and 0 < m, both 4 ≤ k and m ≤ k follow.
  - Positional `hHC rfl` against the underscored contract binders.
  - Defeq passing of the old-namespace `original_HC46_exact` into the new-namespace slots.
  - Name resolution: the Dyadic file and the SourceSize Application file open only the SourceSize namespace, so unqualified `selected_actual_analytic_rhs` and similar names resolve to the SourceSize copies.

  No new defect.
- The other **63 supplied bodies** (40 prior project files and 23 Complexitylib files) were supplied again intact. I reuse my original Full95 full inspection of them, re-checking only the declarations the new bodies call.
- The other **279 prior bodies** are covered by identity reuse only: identical bytes, configuration and 7979 constant types/edges. They were **not re-read**.
- **Skipped required bodies: none.**

**Status of the original Full95 findings:**
- N-1 and N-3 are confirmed.
- N-2, N-4 and N-5 stand as written.
- N-6 (Spectral47), N-7 (numeric NO) and N-8 (selection) remain **open**.

## 5. Remaining HIGHs and their exact scope

- **H-1: closed** (see §1).
- **R14, HIGH, open, on the encoded reduction/runtime gate only.** It concerns whether an encoded reduction can avoid materializing objects indexed by J = `blocks samplerA (hBlock L m)` while satisfying polynomial-time and size requirements.
  - It does not affect the truth of the conditional material theorems.
  - J being large is **neither a runtime proof nor a disproof**. The gate is unresolved, not decided.
- No other HIGH remains in the material scope. The Full90 I3/R5 coupling was already reduced to Medium F2 (joint witness) by the SourceSize roots.

## 6. Original reports

All three original Full95 reports (proof-adversarial 19DEA96A…, complexity AFEA28B5…, non-claims 20D71123…) are preserved unchanged. This is an addendum, not a rewrite.
- **Proof-adversarial:** its "GO-WITH-NOTES, conditional on reconciling H-1" verdict for native/material conditional integration **now stands**. Its overall GO is still not issued because of R14.
- **Complexity:** its NO-GO, held solely because of H1, is lifted **for the material scope only**. Its "overall" verdict stays at not issued because of R14 and the full-scope gates.
- **Non-claims:** unaffected; its GO-WITH-NOTES stands.

## 7. Safe conditional claim

This rests on the pinned kernel and Init/Mathlib/Batteries trust, the qualified Full95 native receipts (181 standard profiles, all seven stage exits 0), the source/object mapping receipt, the structural trace, and identity reuse of the 319 prior bodies.

For every `I : Instance N rows` with `rows` independent of m, and every copies, `U : TaggedGoodU`, A, C, T, f, base and `sourceHeightCutoff`, suppose:
- `selector(analytic floor) L = m`;
- `1 ≤ samplerA`;
- `r < c+s`;
- `0 ≤ e`;
- `hfail(e)` holds on the same coordinate leaf table;
- `Spectral47ExactContract sourceHeightCutoff` holds;
- `a > 0`.

Then, with HC46 discharged by `original_HC46_exact`, and with `hdim`, `hD` and `hsmall` derived:
- **SourceSize export:** there is a dyadic k with 4m ≤ k < 8m such that `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc,Tc,fc,r,k,2e,a)`.
- **Dyadic exports:** the same bound holds for every caller-chosen dyadic k ≥ 4m.
- **Both:** the matching center mass equals the exact Grassmann center fraction.

Citations must use fully qualified names, because the old `Instance N m` roots share the bare names.

**Not claimed:**
- universal Spectral47, or its fidelity to manuscript 4.7;
- numeric NO or a useful e or a;
- joint source/selection witnesses (I, copies, U, A, `hsel`);
- source/star/robust8S results or acceptance-to-functional;
- encoded runtime, reduction or learning (R14);
- upstream bridges;
- zero total warnings;
- novelty, citations, render or publication;
- unconditional theorem or manuscript acceptance.

## Remaining to-do

1. Receipt hygiene (H-1a): key object hashes by `.olean` path, and ship the before/after, manifest and inventory member contents alongside future mappings so membership can be checked directly.
2. Spectral47: a machine proof for the actual append operator (GL orbit, Fourier covariance, orbit counts, Parseval), `Iff.rfl` bridges between the duplicated contracts, and a fidelity audit against 4.7.
3. A certified scalar consumer:
   - choose r, T and dyadic P ≥ mT;
   - prove the Parseval bound ΣE_i ≤ 1, the B ≤ 2^{−r(s−1)} side conditions and the finite-sum comparisons;
   - instantiate `base` and `cutoff`;
   - give an effective L₀.
4. Prove `hfail` with a useful e on NO instances, then compare 2·RHS against the NO threshold.
5. A joint inhabitance witness for I (rows ≥ 1), padded copies, `U : TaggedGoodU` at J, A and `hsel`.
6. Source/star on the trace: acceptance → a fixed f, `AllAmbientInverse`/robust8S, and discharge of `kappa`/`hexpand`. Close `source_selection_complete`.
7. R14: the encoded reduction and runtime, implicit handling of J, an explicit expander table and `rotVal` cost. This should be decided by proof, not by parameter size.
8. Post-audit of the upstream seven-target receipt, then the CMMSA bridges.
9. Hygiene: dispose of warnings and info output, including linter suppression and in-library `#print axioms`; remove stale banners (N-4); mark the old m-coupled roots as superseded; replay from a fresh checkout.
10. Manuscript fidelity (E1 exponents, constants, PR wording, the m/rows semantics), then novelty, citation and BibTeX/PDF QA, and the final full-scope providers.
