# Proof-adversarial review, packet 2 of 2: Full109 cross-level Gram identity and conditional material integration

The new theorem `append_rank_cross_level_gram_eq_product` is sound, and I found nothing that blocks it in this packet. It is also integrated correctly: it is a standalone root, and nothing in the material lane uses it. Overall readiness is **NO-GO**. R14 (encoded reduction and runtime) is still an open HIGH, and the numeric, source, upstream, replay, certification and publication gates are also open.

## Verdicts

| Scope | Verdict |
|---|---|
| Soundness of the two fresh files | **Sound.** No soundness, orientation, quantifier, normalization, carrier or vacuity defect. |
| Native translation of the real same-function cross-level Gram identity | **Done, as stated.** It is an exact `if i = j` equality on the original unconditional append, with each carrier using its own normalized mean. |
| Conditional integration with the selected-leaf, SourceSize/HC46/dyadic and material callers | **GO-WITH-NOTES, conditional.** The material bytes are unchanged and the new root is not consumed. No HIGH finding in this scope. |
| Whether this lens has covered every packet | **Not yet.** This report covers packet 2 only. The packet-1 report and the root reconciliation are still needed. |
| Overall readiness | **NO-GO.** No manuscript or publication acceptance, and no novelty or priority claim. |

**Method.** I used no tools, made no writes, ran no Lean or Lake, and started no subagents. All hash checks are string comparisons. Kernel results, axiom profiles, trace and custody facts come from the receipts. I cannot confirm that the provider context window fit, so that stays pending.

## 1. Coverage

**Fresh files, read in full with every declaration checked:**

| File | Header SHA vs typed `source_sha256` | Object |
|---|---|---|
| `ActualAppendProductCrossLevelIdentity.lean` | BB738BC9…CE90, which matches both the typed record and `derivation.json` `new_sha256` | 5E713CCE…AFD, which matches the legacy field |
| `…CrossLevelIdentityChecks.lean` | 113B8DDB…0739, matches | 7E4E799D…7375, matches |

Source and object hashes were never compared with each other.

**Other bodies in this packet:** by my hand count, 51 files in total. These are the two fresh files plus 49 others:
- **Re-checked against the interfaces the fresh theorem uses:** `ActualFiniteFrameProductDuality`, `ActualFiniteAppendExactImageEnergy`, `ActualFixedFunctionalAppendOperator`, the SourceSize Analytic/Append/Original/Spectral exports, Dyadic, and `SourceSizeContractBridge`.
- **The rest:** read, but their credit comes from the per-lens reviews in the 45 preserved reports by identity reuse. I did not re-derive them line by line in this pass.

**What this packet does not contain:** the body of `ActualAppendFourierCrossLevelOrthogonality`, which the off-diagonal branch depends on. The same goes for `BinaryMatrixFourier`, `GrassmannCounting`, `ActualFiniteAppendSpectral47` and the other parent files. For the orthogonality lemma:
- The kernel accepted the `exact` call, so the statement is fixed.
- Its body was reviewed in Full90 packet 1 (PA1-09, verified). In this packet it is covered by identity only.

**Required fresh bodies skipped: none.** I make no claim to have freshly re-read all 348 files.

## 2. Declaration audit: `append_rank_cross_level_gram_eq_product`

**Hypotheses:**
- `n c s i j : Nat`.
- `hi : i ≤ c+s`, which is retained.
- `F : BinaryMatrix n (c+s) → Real`, arbitrary and real-valued.
- `basisInv`: for every matrix M and every pair U, V with U·V = 1 and V·U = 1, F(M·U) = F(M). Rank-deficient M are included.
- There is **no bound on j**.

**Conclusion:** the uniform mean over `BinaryMatrix n c` of `appendAverage(P_i F)(M) · appendAverage(P_j F)(M)` equals:
- if i = j: ∏_{k<s} (2^{c+s−i} − 2^k)/(2^{c+s} − 2^k) times the uniform mean over `BinaryMatrix n (c+s)` of (P_i F)²;
- otherwise: 0.

The same F and the same `appendAverage` (uniform B over all n×s matrices) appear on both sides. The carrier is the original unrestricted append, unchanged.

**Proof check:**
- **Case i = j.** `subst j` is valid because j is a free implicit. `ite_eq_left rfl` selects the `then` branch. `simpa only [pow_two]` then turns both `^2` occurrences into products in the goal and in the Full107 lemma `append_rank_projection_energy_eq_product hi F basisInv`. The exponents `c+s−i` and `k.val` are not the literal 2, so `pow_two` does not touch them. The result is an exact equality.
- **Case i ≠ j.** `ite_eq_right hij` selects the `else` branch. Then `exact uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero hij F` applies: this is the native Full90 orthogonality on the unconditional append, with no invariance hypothesis.
- **Alias repair.** `ite_eq_left` and `ite_eq_right` replace `if_pos` and `if_neg` and mean the same thing. The Full108 bytes and the diff were not supplied, so "exactly two aliases changed" rests on receipts.
- **Warnings.** The file has no `set_option linter`, so nothing is being suppressed. The receipts show zero owned and zero inherited-regression warning headers.

**Edge cases:**

| Case | Result |
|---|---|
| c < i ≤ c+s | Real zero factor at k = c+s−i < s, native in Full107. The left side, the retained energy, is 0. |
| s = 0 | `hi` forces i ≤ c. The empty product is 1. |
| i = 0 | Every factor is d/d with d > 0, so the product is 1. |
| n = 0 or zero width | Only rank 0 exists. Handled by the inherited laws. |
| Empty rank-i support (e.g. i > n) | Both sides are 0. |
| j > c+s or j > n | P_j F = 0, and the orthogonality lemma covers it anyway. No j guard is needed. |
| Statement weakened? | No. The conclusion is an equality, not an inequality, and the carrier is unchanged. |

## 3. Findings

| ID | Sev. | Item | Disposition |
|---|---|---|---|
| X109-1 | Verified | The theorem | Sound and native. Standard profile per the receipt. |
| X109-2 | Low (stale) | The header still says "successor candidate has not been compiled" | Contradicts the receipt. Fix in the next revision; the captured bytes stay immutable. |
| X109-3 | Info | `hi` is not needed for the product form: when i > c+s, P_i F = 0 and both sides are 0 | Kept as required. It narrows no real caller. |
| X109-4 | Info | `basisInv` is required even though the off-diagonal branch does not use it | Stricter than necessary, but within the manuscript's invariant-F setting. |
| X109-5 | Info | The `if i = j` uses `instDecidableEqNat`, and the file has no `Classical.propDecidable` local instance | A future caller in a module that has that instance may need `convert`/`simp`. There is no consumer today. |
| X109-6 | Info | The leftover `classical` tactic does nothing | Hygiene only. |
| X109-7 | Info (non-claim) | The δ_ij form is proved. The manuscript's λ_j·⟨P_iF, P_jF⟩ form is not packaged, and no adjoint is used | Do not cite this theorem as G/Φ, the restricted adjoint, the eigen-relation, or the complex or two-function forms. |
| X109-8 | Info (evidence tier) | The orthogonality body is absent from this packet | The packet-1 lens and identity reuse must cover it. |
| X109-9 | Info | Checks harness | Contains only `#check` and `#print axioms`. That is log output, not evidence. |

**Bookkeeping:**
- Requested roots: 172 + 89 = 261, and I counted the 89 added roots by hand. Focused set: 93.
- Source files: 346 + 2 = 348.
- Trace: 8298 + 1 = 8299 nodes, with external boundaries still at 2767 and 0 unresolved. This fits a single new root whose dependencies were all already reached, but the nodes are not individually enumerated.
- `readiness.json` `probe_executed: false` and the native-report flags `material_body_review_complete` and `consumption_trace_complete` are historical. They were superseded by the later qualification summary.
- `source_selection_complete: false` is still current.

## 4. Integration (bytes unchanged, prior checks carry forward)

- **Unchanged files.** The SourceSize Analytic/Append/Original files, Dyadic, and `SourceSizeSpectralApplication` (1E985E9A) all have the same SHAs.
- **Spectral-discharged exports keep their full premise set.** They are free of HC46 and Spectral47, and still require:
  - `hsel` at the floor `max(analyticSourceHeightFloor…, j+2)`
  - `hA : 1 ≤ samplerA`
  - `hrd : r < leafT + leafK`
  - `he`, and `hfail` on the same `selectedCoordinateLeafTable`
  - `ha`
  - for the dyadic export only: `hkDyadic` and `hkm : 4m ≤ k`
- **Sizes.** `rows` is independent of m. c + s = 2h ≤ 2J, with `hdim`, `hD` and `hsmall` derived.
- **Same objects throughout.** The same I, copies, U, A, C, T, f and the same `Tc` are used everywhere. There is no surrogate, no rank-one or uniform noise, and no narrowed family.
- **The new theorem is not consumed.** The material right-hand side still uses 2^{−i(s−1)} + 3·2^{i−n}. The material proof already used cross-level vanishing, via `appendHighLevel_energy_eq_sum`. The new identity does not tighten anything.
- **Still spectral-conditional (F1-r, Low).** The legacy m-coupled exports and the hHC-parametric exports still carry `hSpectral`.
- **No new witnesses.** Nothing here supplies a source, selection, global-table, star, robust8S, pre-draw, sampler, encoded-reduction, runtime or learning witness.

## 5. Safe conditional claim

This rests on the pinned kernel and library trust, 261 standard profiles, seven stage exits of 0, the qualified 8299-node trace with nothing unresolved, the typed identities, and identity reuse of 346 bodies.

For every n, c, s, i, j with i ≤ c+s, and every real F that is invariant under all paired-inverse right actions, the unconditional append satisfies E_M[T P_iF · T P_jF] = [i = j] · ∏_{k<s}(2^{c+s−i} − 2^k)/(2^{c+s} − 2^k) · E_W[(P_iF)²]. The Full105/107 conditional material bounds are unchanged.

**Not claimed:**
- G/Φ composition, sampling law, eigen-relation, restricted adjoint, complex or two-function forms
- numeric NO, the `hfail`/scalar/source-height fidelity crosswalk
- any witness, R14
- upstream transports or post-objects
- fresh replay, inherited-warning certification
- providers, novelty, citations, manuscript, overall GO

## Remaining to-do

1. Get the packet-1 proof-adversarial report, including a fresh check of the orthogonality body, and complete the root per-lens reconciliation across all three lenses.
2. Supply the Full108→109 diff, or record it as receipt-tier. Fix the stale header (X109-2).
3. Prove natively the G/Φ completion and marginals, the Φ eigen-relation with independent B and C, and the invariant-first adjoint. Package the λ_j⟨P_iF, P_jF⟩ form. Handle the complex and two-function extensions separately.
4. Lemma 4.7 / MZ24 A.13 crosswalk: the exact λ_i is a reconstruction, the cutoff is inert, and the guards and slack go unused.
5. Supersede or wrap the spectral-conditional legacy exports (F1-r).
6. Numeric NO: a certified scalar consumer, `hfail` at a useful e, base and cutoff, an effective L₀, and the source-height fidelity check.
7. Joint source, selection and global-table witnesses: star, robust8S, pre-draw, the physical sampler.
8. R14 (HIGH): encoded or implicit reduction with a runtime proof, and learning.
9. Upstream post-audit, then the exact CMMSA transports and post-objects.
10. Fresh-checkout source and object replay recomputing every hash and DAG digest, enumeration of the trace delta, and certification of inherited warnings.
11. Final gates: provider, novelty, citation, BibTeX, TeX, PDF and manuscript.
