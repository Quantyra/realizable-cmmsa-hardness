# Full109 complexity review, packet 2 of 2: `ActualAppendProductCrossLevelIdentity` and the conditional material integration

## Verdicts

The new cross-level Gram theorem is sound. Conditional material integration is GO‑WITH‑NOTES, scoped to this packet. Overall GO is not issued: R14 is still an open HIGH, and the exact operator laws and several other gates remain open.

| Scope | Verdict |
|---|---|
| **The two fresh bodies** (`ActualAppendProductCrossLevelIdentity`, `…Checks`) | **Sound.** I found no defect in soundness, orientation, quantifiers, normalization, case split or vacuity. |
| **Native translation** | **Closed for exactly this statement.** The receipt gives the root a standard profile. **Still open:** the G/Φ laws, the Φ eigenrelation, the restricted adjoint, the two‑function Gram identity and any complex version. |
| **Conditional SourceSize/HC46/dyadic/selected‑leaf integration** | **GO‑WITH‑NOTES, for packet 2 only.** No HIGH is open in this scope. The material bytes are unchanged and the new root feeds no material export. Integration acceptance also needs the packet‑1 report for this lens and the root reconciliation. |
| **Overall readiness / GO** | **Not issued.** R14 (HIGH) is open, as are the numeric, source, runtime, upstream, replay, certification and publication gates. |
| **Manuscript, novelty, priority** | **No acceptance.** |

**How I reviewed.** I used no tools, made no writes, ran no Lean or Lake, and used no subagents. Every hash check is a string comparison of values supplied in the packet. Native GREEN is treated as kernel acceptance, not semantic acceptance.

## 1. Coverage

| Body or evidence | What I did |
|---|---|
| `ActualAppendProductCrossLevelIdentity.lean` (BB738BC9…CE90) | Read every line, including the single declaration and the whole proof. |
| `ActualAppendProductCrossLevelIdentityChecks.lean` (113B8DDB…0739) | Read in full. It contains only `#check` and `#print axioms`, so it adds build‑log output, not evidence. |
| The other bodies supplied in this packet | Re-checked fresh at the interfaces this theorem and its integration touch (list below). |
| The other 346 parent bodies and 8298 shared nodes | Covered by per‑lens identity reuse under the revalidated 45 prior reports. This is **not** a fresh reread of 348 bodies. |
| All 45 prior reports, plus the argument, derivation, reconciliation and evidence JSON | Read in full. |

The interfaces re-checked this pass were:
- `ActualFiniteFrameProductDuality`, in particular `append_rank_projection_energy_eq_product`;
- `ActualFiniteAppendExactImageEnergy`, `ActualFiniteAppendGlobalImageEnergy`, `ActualFiniteAppendImageTailBridge`, `ActualFiniteBinaryImageFibres` and `ActualFiniteBinarySurjectionCounting`;
- the SourceSize Analytic, Append and Original modules, the dyadic module, the `SpectralApplication` module and its Checks;
- `SourceSizeContractBridge`, `BinaryMatrixRightOrbit` and `BinaryMatrixRightFourierCovariance`;
- `ActualFixedFunctionalAppendOperator` and `ActualFixedFunctionalBinaryMatrixMoment`;
- `MatrixLiftAffineTarget` and the HC46 inhabitant.

**Required fresh bodies skipped: none.** Skips that matter for this theorem, all at identity tier only:
- **S‑1.** The body of `ActualAppendFourierCrossLevelOrthogonality` is not in this packet. The off‑diagonal branch depends on it. Its statement is corroborated here by the call site in `appendHighLevel_energy_eq_sum`, and its body was reviewed in Full90 (PA1‑09, P6, N11).
- **S‑2.** The bodies of `ActualFiniteAppendSpectral47`, `BinaryMatrixFourier` and `GrassmannCounting` are not in this packet.

## 2. Audit of `append_rank_cross_level_gram_eq_product`

**Hypotheses, exactly as stated:**
- `{n c s i j : Nat}`;
- `hi : i ≤ c + s`;
- an arbitrary real `F : BinaryMatrix n (c+s) → Real`;
- `basisInv`, quantified over **every** `M` and every paired inverse with `U*V = 1` and `V*U = 1`.

There is no bound on `j`, no Booleanity, no rank conditioning of the sampled data, and no source‑height, ρ or parity premise.

**Conclusion.** The left side is `uniformMean` over `Mat(n,c)` of `appendAverage(P_i F)·appendAverage(P_j F)`, which is the actual unconditional append over every `B ∈ Mat(n,s)`. It equals `if i = j then λ_i · uniformMean_{Mat(n,c+s)}((P_i F)²) else 0`, where `λ_i = ∏_{k<s}(2^{c+s−i}−2^k)/(2^{c+s}−2^k)`. Each carrier is averaged over its own normalized measure. This is an exact if‑then‑else equality, not an inequality.

**Proof:**
- **Case `i = j`.** `subst j` eliminates `j`, and `ite_eq_left rfl` selects the then‑branch. The goal then has the form `x * x`, and `simpa only [pow_two]` normalizes both the goal and Full107's `append_rank_projection_energy_eq_product hi F basisInv` (which has `(·)^2` on both sides) to the same shape. This is the native, three‑lens‑reviewed product law; the guard and the invariance argument are passed through unchanged.
- **Case `i ≠ j`.** `ite_eq_right hij` selects the else‑branch. The proof is then exactly `uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero hij F`, applied to the same `F`. That lemma needs only `i ≠ j`: no invariance, no `hi`, and no bound on `j`.

**Edge cases:**

| Case | Result |
|---|---|
| `c < i ≤ c+s` | Full107's genuine zero factor at `k = c+s−i < s`, so both sides are 0. |
| `s = 0` | Forces `i ≤ c`; the product is empty, so λ = 1, and `Mat(n,0)` is a singleton. |
| `i = 0` | λ = 1 (every factor is d/d). |
| `n = 0`, or zero width | Single‑matrix carriers; only rank 0 occurs. |
| Empty rank support (`i > n`, or `i > c` after append) | `P_i F` or its append is 0, and the identity still holds. |
| `j > c+s` with `i ≠ j` | `P_j F = 0`; the zero law covers it with no premise. |
| `i = j > c+s` | Excluded by `hi`. It would in fact hold without `hi`, since `P_i F = 0` there (finding X109‑3). |

**Deprecated‑alias repair.** `derivation.json` records an exact two‑alias replacement with headers unchanged: old SHA B3F1C4F5… became new SHA BB738BC9…. The current bytes use `ite_eq_left` and `ite_eq_right`, contain no `set_option linter…`, and the receipt shows zero owned warnings and zero inherited‑regression headers in all seven stages. I could not diff against the Full108 bytes, which were not supplied, so this rests on the receipt (X109‑5).

## 3. Custody and bookkeeping

**Typed identities.**
- Main file: source BB738BC9… matches the header; object 5E713CCE… matches the legacy field.
- Checks file: source 113B8DDB… matches the header; object 7E4E799D… matches.
- No source hash equals any object hash. The settled H1 category error stays closed.

**Counts.** These are consistent:
- roots 260 + 1 = 261; focused 92 + 1 = 93; sources 346 + 2 = 348;
- trace 8298 + 1 = 8299 nodes, with 8299 exact type‑edge matches;
- external boundaries unchanged at 2767;
- 0 unresolved nodes in both graphs.

The +1 node with no new boundary fits the picture that `ite_eq_left`, `ite_eq_right`, `pow_two` and the orthogonality lemma were already reached elsewhere. That is plausible but not enumerated.

**Flags.** `material_body_review_complete` and `consumption_trace_complete` are false; these are historical, from before the trace. `source_selection_complete`, `independent_body_review_complete` and `accepted` are all false, and these are current.

## 4. Integration

The material sources are byte‑identical: AppendMoment D4B86B56, Analytic 03FB0A5D, Original 22DE415F, Dyadic AF3E380A and `SpectralApplication` 1E985E9A all match the typed pins. Everything already verified about them carries forward unchanged:

- **Inputs.** `Instance N rows` keeps the source row count independent of the leaf arity `m`, and one I, copies, U, A, C, T, f is used throughout.
- **One leaf table.** The same `Tc` serves `hfail`, the PR premise and the moment.
- **Dimensions.** c + s = 2h ≤ 2J, with `hdim`, `hD` and `hsmall` derived rather than assumed.
- **HC46.** It is discharged by `original_HC46_exact` at `hEven := hsplit`.
- **Spectral47.** It is discharged in the two `…spectral_discharged` exports.
- **Dyadic exponent.** The caller chooses a dyadic k ≥ 4m.
- **Remaining premises:** `hsel`, `hA`, `hrd`, `he`, `hfail` and `ha`.
- **No substitution.** There is no uniform or rank‑one surrogate and no narrowed source or star family.

The new root is **not consumed**. `selected_actual_analytic_rhs` still uses `2^{−i(s−1)} + 3·2^{i−n}`, so the material right‑hand side is **not tightened**, and the theorem supplies no source, selection, global‑table, star, robust8S, pre‑draw, sampler, encoded‑reduction, runtime or learning witness.

## 5. Findings

| ID | Sev. | Declaration | Evidence | Disposition and action |
|---|---|---|---|---|
| X109‑1 | Verified | `append_rank_cross_level_gram_eq_product` | §2 | Credit as the native real, same‑function, cross‑level Gram identity for the unconditional append, conditional on `basisInv` and `i ≤ c+s`. |
| X109‑2 | Verified; narrows C105‑05, C107‑05, PD‑4, NC107‑4 | The earlier "packaged cross‑level identity" item | It was composable but not packaged; it is now packaged in the δᵢⱼ form. | Still open: G/Φ completion and marginals, independent B/C sampling, the Φ eigenrelation, the invariant‑first adjoint, the two‑function law `⟨T P_iF, T P_jH⟩ = λ_j⟨P_iF, P_jH⟩`, and the complex form. |
| X109‑3 | Info | `hi` | The identity also holds for `i = j > c+s` (both sides are 0). | The guard is retained; the statement is not weakened. Optional generalization only. |
| X109‑4 | Low | Header text "has not been compiled" | Contradicted by the native receipt. | Fix in the next revision; the captured bytes stay immutable. |
| X109‑5 | Info (custody) | Full108 → Full109 alias diff | Old bytes were not supplied. | Receipt tier; recompute during replay. |
| X109‑6 | Low (evidence tier) | Off‑diagonal dependency body (S‑1), Spectral47 / Fourier / GrassmannCounting (S‑2) | Not in this packet. | Identity reuse; confirm against the packet‑1 report and a fresh‑checkout replay. |
| X109‑7 | Info | Checks harness | Only `#print axioms` output. | Handled under log disposition. |
| Carried | Low/Medium | Lemma 4.7 / MZ24 A.13 crosswalk (the inert cutoff; the exact λ is a reconstruction, not a quotation); the zero‑branch wording (negative real factors once the product is 0); F1‑r legacy spectral‑conditional exports; stale banners; flag labels; the legacy hash field; the 566 / actual‑object count | Unchanged | Open |
| Carried | Medium | Numeric NO (`hfail` with a useful e, the scalar parameters, an effective L₀); the joint arity, source, selection and global‑table witnesses; star, robust8S, pre‑draw selection, the sampler and the encoded reduction; learning; exact upstream transports and post‑objects; fresh source and object replay; inherited‑warning certification | Unchanged | Open |
| **R14** | **HIGH** | Encoded reduction and runtime for the doubly exponential J | No runtime theorem exists. | **Bars overall GO.** |

## 6. Safe conditional claim

This rests on pinned kernel and library trust, the Full109 receipts (261 standard profiles, seven stage exits of 0, zero owned and regression warning headers), the 8299‑node trace with nothing unresolved, the typed identities, and identity reuse.

**The new identity.** For all n, c, s, i, j with i ≤ c + s, and every real F invariant under all paired‑inverse right actions:

E_{Mat(n,c)}[A_s P_iF · A_s P_jF] = [i = j] · ∏_{k<s}(2^{c+s−i}−2^k)/(2^{c+s}−2^k) · E_{Mat(n,c+s)}[(P_iF)²].

**Prior claims stand.** The Full105 SourceSize and dyadic material bounds are unchanged: they need no HC46 or Spectral47 premise and remain conditional on `hsel`, `hA`, `hrd`, `he`, `hfail` and `ha`.

**Not claimed:**
- G/Φ, the independent sampling law, the pointwise eigenrelation, the restricted adjoint, the two‑function identity or the complex extension;
- any tightened material bound or any witness;
- numeric NO, runtime, reduction or learning;
- upstream transports, replay, or warning certification;
- novelty, priority, or manuscript acceptance;
- overall GO.

## Remaining to‑do

1. Packet‑1 complexity report for Full109, then root reconciliation across both packets for this lens.
2. Prove natively the GL completion counts and uniform R/C marginals, Φ with independent unrestricted B and full‑row‑rank C, the kernel‑frame eigenrelation, the invariant‑first adjoint, the two‑function Gram law and the complex continuation. Each needs its own native qualification, trace and fresh review.
3. Lemma 4.7 / MZ24 A.13 crosswalk: the inert cutoff, the unused guards and the `+3` slack, wording for the zero branch, and the reconstructed status of the exact λ. Decide whether to tighten the material right‑hand side using λᵢ.
4. Supersede or wrap the spectral‑conditional legacy exports (F1‑r). Fix the stale headers (X109‑4 and the earlier ones), the flag labels and the legacy hash field.
5. Numeric NO: a certified scalar consumer, a useful e with `hfail`, choices of base and cutoff, and an effective L₀.
6. Joint I / copies / U / A / `hsel` witness; source, star and robust8S; the pre‑draw global table; the physical sampler.
7. R14: an encoded or implicit reduction with a runtime proof; learning.
8. Upstream post‑audit, then the exact CMMSA transports and post‑objects.
9. Fresh‑checkout source and object replay that recomputes every hash and DAG digest and enumerates the +1 node. Supply the Full108 → Full109 diff and read the S‑1 and S‑2 bodies fresh. Certify the inherited warnings.
10. Final provider, novelty, citation, BibTeX, TeX, PDF and manuscript gates.
