# Proof-adversarial review: original complement zoom-failure transport

Date: 2026-09-30. Verdict: **GO-WITH-NOTES**, for the bounded transport increment below only. No HIGH or MEDIUM mathematical defect found. This is one independent content review; it does not complete the required three-lens table or full CMMSA certification.

## Scope and independence

Destination: `C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness`. Owning planning work: realizable hardness formal proof and paper (S3126), and outer game and star PCP (S3132). Reviewed the full source of `ActualCoordinateZoomFailureTransport.lean`, its Checks module, relevant carrier/table/coordinate definitions, exact frozen input archive, actual raw compiler receipt, runner script, local command provenance and scoped manifest/audit. No compiler or GCP action was run, and no proof source was edited. Only this report is written; root serializes Git and planning closeout.

I was launched directly by root as the proof-adversarial reviewer, separately from the source owner. Disclosed overlap: root and Sol supplied Luna read-only compiler/API routing hints; reviewers share Sol's model/persona family. Independence here means separately reading and verifying the source/evidence, not independent model architecture or a blind review. The prescribed Task/OpenCode mechanism was unavailable; collaboration fallback governance debt remains for the orchestrator to record. This report supplies the content lens and does not silently clear that mechanism debt.

Read planning `docs/protocol.md`, `docs/formal-three-lens-closeout-protocol.md`, the inherited IGH baseline, relevant story context and IGH inbox. Destination root `AGENTS.md` is absent; no destination instruction file was substituted or created.

## Exact evidence pins

All SHA-256 values below were independently checked against archive bytes or actual recorded pin files as stated.

| Artifact | SHA-256 |
|---|---|
| Main source, frozen input and current local bytes equal | `D157ED4CDEF826EDF470D93C4715934613291AAA14F6484459C3835F9EAEA02E` |
| Checks source, frozen input and current local bytes equal | `BD7A3607C3027755D76A55EB5FF5AEFED6A361D518F7B1A858C077476EECD96D` |
| Frozen input `cmmsa_analytic_20260930T090338Z.tar.gz` | `AD9108E72AF2641AB92B4E73CAD3C1C8E0492E76A0B935CB26FB7B26327B3680` |
| Actual evidence `cmmsa_analytic_20260930T090338Z-evidence.tar.gz` | `77115C3A86B1A349432CE1C060AC6F4AA18BA8581F9840E3B5C3F77AEDEF3929` |
| Main object, **remote hash receipt only** | `D115E9D45372A1745B639CE3434D9561CCC90A83B343CE7341B19FBD03686306` |
| Checks object, **remote hash receipt only** | `93A704DEEB0E5B8E0C1E39D2BECCE4AAB94B86C44110C83FA130ECB08E29FEEB` |
| Raw main build stdout | `4DE11EDE45A864C79B4231BBD49A73AD1D7C007FFBDE86334ED0B3991A3ABB1F` |
| Raw Checks build stdout | `91772F8C3D5A58B47FD3F03435CEFEBA5A17505C3731EE4EAF04D95D15852F81` |

Receipt location: `docs/native-receipts/ActualSelectedComplementAnalyticMoment/durable-runs/cmmsa_analytic_20260930T090338Z/`.

Every `source-before.sha256` entry matches the corresponding frozen input member, including the manifest/toolchain and all overlays. Main/Checks source pins also match `pins.sha256`. Raw extracted files equal their evidence TAR members byte for byte. The input copies of the coordinate bridge, maximal-pair ladder and complement-incidence definitions equal the local files inspected.

Actual `prebuild-0.native-exit` and `native-exit` are both integer 0. Main stdout ends with a freshly **Built** transport target (3348 jobs); Checks stdout ends with a freshly **Built** Checks target (3349 jobs). Neither raw stdout contains an error diagnostic. Runner inspection confirms that it deletes the two target `.olean` files before these builds, verifies non-overlay repo file bytes against the input archive, then records source-before and final pins. Actual SSH stdout contains `REUSED_DEPENDENCY_BYTES_VERIFIED` and all nine overlay source checks marked OK. This is an incremental build with reused dependencies, not a fresh rebuild of every dependency. The two object files themselves are not included in the evidence TAR; I verified the recorded hashes, not independently supplied object bytes.

Toolchain receipt: Lean 4.34.0-rc2, Linux x86_64, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`. Manifest pins include mathlib `e06eff5f95374108acfaf19f1ff7473aa7771df2`, cslib `d9be64196bf145edd019f1ccfeaee0c11166ba6b`, complexitylib `6c248df7859f2f245e731c1e07057bf69d165fe2`. Both stderr files disclose local cslib changes; this run records its revision but does not archive the complete package cache. Preserve that reproducibility limitation. It is not evidence of a new theorem axiom: the actual exported dependency profiles are standard-only.

All seven local CLI command stdout/stderr hashes match `commands.json`. SSH, SCP retrieval, stop and final describe exits are 0. Final recorded `6.stdout` says `TERMINATED`; wrapper terminal is 0 and unified terminal chunk is `f04523`. Thus this run has actual terminal cleanup evidence; no live/current cloud state beyond this recorded observation is claimed.

## Statement and proof checks

1. **No narrowed decoded class.** `DecodedPair Q d` consists only of an arbitrary submodule W, containment Q ≤ W, and an arbitrary dual linear map on W. The parameter d imposes no extra coherence or global extension restriction. `pullbackDecodedPair` takes any coordinate Q/P, pulls W through the inverse of the same chosen coordinate equivalence, and composes P.g with its restriction. No global-functional-only substitution occurs. `autoImplicit false` is set; actual Checks signatures show the expected I/copies/U/A, dimensions and Q/P parameters, with no hidden contract or pseudorandomness premise.
2. **Full fibres, both directions.** `map_le_map_coordinate_iff` reflects containment by injectivity. `coordinate_zoom_containment_iff` preserves both Q ≤ L and L ≤ W. `coordinateZoomEquiv` is an actual subtype equivalence of the entire zoom carriers, not a one-way injection or selected subfamily.
3. **Same table and functional pointwise.** `coordinateLeafTable` precomposes each original leaf label with the inverse restricted coordinate map. `coordinate_agrees_iff` verifies this table on all leaf vectors and compares P.g through the same forward restricted map; the functional identity uses subtype extensionality. `coordinateAgreeingZoomEquiv` combines that pointwise equivalence with the full zoom equivalence. Proof witnesses for containment introduce no mathematical restriction.
4. **Exact budget and rational ratio.** `coordinate_codim_eq` preserves both ambient and W ranks before taking the Nat difference. Both zoom-cardinality and agreeing-cardinality equalities are used in `coordinate_agreement_eq`. The `agreement` definition explicitly returns zero when the zoom card is zero. The equality therefore holds without nonemptiness, including that empty case; no division cancellation or denominator positivity is assumed.
5. **Universal failure transport.** For every coordinate q/Q/P at exact q + codim W = r with nonempty zoom, the final theorem constructs its source pullback, transfers the same budget and nonemptiness by the bijection, applies the supplied source `hfail`, and rewrites exact agreement. T, e and r are fixed throughout. No existentially chosen replacement table or final-moment assumption is introduced. Nonnegativity `he` is unused here (also identified by the actual linter); this is harmless redundant API input.
6. **Kernel assumptions.** The five actual `#print axioms` exports—pullback pair, Zoom equivalence, AgreeingZoom equivalence, agreement equality, and universal failure transport—each report exactly `propext`, `Classical.choice`, `Quot.sound`. A comment-stripped scan of the 159 repo-local files in the frozen target import closure found no `sorry`, `admit`, `axiom`, or `native_decide` tokens. That scan complements the actual compiler profiles; it does not claim an audit of every external package.

## Findings and bounded interpretation

**NOTE: supplied failure remains supplied.** This theorem proves a transport implication. It does not derive failure for an arbitrary original table, supply a non-vacuous failure witness, prove density or an inverse decoder, or prove that a particular source verifier instance satisfies the hypothesis. Empty or impossible dimension families can make a given failure assertion vacuous, but the equality/bijection results remain valid and the final assertion explicitly retains the nonempty guard. Do not describe this as existence of a failing instance or unconditional CMMSA hardness.

**NOTE: integration remains separate.** The accepted BFAE analytic module's `selected_actual_material_moment_bound` still accepts the full coordinate failed-zoom hypothesis; it does not import this transport module. A further reviewed caller can apply this theorem to `transportedLeafTable` for the same chosen complement. This report does not certify that new caller or change the immutable accepted conditional analytic increment.

**NOTE: source overlays are not build certificates.** Numerics `8825A12CFAC7C66602C3311E8FCE5744BC2DF7C929C0C922A89F7D64DDC494A3` and Margin `B39F0D1AC5FA674E2FA997D19E0FF55B03A01962CDF87E94ECE1C299D76CC485` were copied and hashed as overlays. They are outside this transport target's certified build scope. No numerical theorem, same-functional inverse/margin, robust 8S, numerical NO contradiction, runtime, HC/spectral inhabitants, or full core is accepted by this run.

The scoped `zoom-claims-manifest.json` and `audit_zoom_claims.py` correctly describe source/receipt/profile consistency and pending independent lenses. Their claim of the same table means the deterministic coordinate image of the fixed original table, not literal equality across ambient types. I inspected their contents and independently repeated the important checks without running the audit script or writing its result. Manifest success is not a substitute for this review or the other lenses.

## Disposition and remaining debt

**GO-WITH-NOTES** for exact universal failed-zoom transport from the chosen original complement to its coordinate model at the two frozen source pins. No proof correction is required by this lens. Preserve the source-conditioned interpretation, source-only overlay boundary, package-cache reproducibility limit and collaboration mechanism disclosure.

Remaining work under S3126/S3132: root records the other two independent lenses and the three-lens disposition; documents/clears Task/OpenCode fallback governance debt; routes same-original-table caller integration through its own build/review; continues numerical bounds and chosen-functional inverse/margin, robust 8S, NO/runtime and full conditional core; then discharges outward classical component contracts and reproducible full manuscript certification. These are existing open workstreams, not accomplishments of this review. Full user goal and owning stories remain active.
