# Full90 material integration: non-claims review

## Verdicts

| Scope | Verdict |
|---|---|
| **Material statement and native integration** (does the exported theorem state, and get, exactly what the reviewed bodies prove?) | **GO-WITH-NOTES.** No defect in how the theorem is assembled, its soundness, or its fidelity to the original material theorem. |
| **Overall material integration GO** | **Not issued.** One HIGH item is still open: I3, whether the premises can all be satisfied together (see below). Under your rule, an unresolved HIGH rules out an overall GO. |
| **Unconditional material readiness** | **INCOMPLETE / NO.** Spectral47 is still a premise. Satisfying all premises together, a useful e (`hfail`), numeric NO, and the source/star bridge are all open. |
| **Manuscript** | **Not assessed.** No acceptance is given. |

**How I worked.** No tools, writes, Lean/Lake or subagents. I did not recompute any hash. Native, compiler, custody and reached-constant facts are the evidence you supplied. The reached-constant index is the author's recorded union reach; I did not reproduce it. The author's reconciliation notes are hypotheses, and I checked each one independently.

## Coverage

| Item | Count | Status |
|---|---|---|
| Complete project bodies supplied | 40 (1 changed export, 4 unchanged critical rereads, 35 new reached modules) | 40 inspected, 0 skipped |
| Complexitylib context bodies | 23 | 23 inspected, 0 skipped |
| **Total supplied bodies** | **63** | **63 inspected, 0 skipped** |
| Fresh packet reports | 15 | all 15 read |
| Prior reports and syntheses | 30 | used only under the verified 169-body / 7251-node identity audit |
| Prior bodies eligible for reuse (169) | — | **not re-read here, and not claimed as re-read** |

Corpus arithmetic: 177 unique packet files − 23 Complexitylib − 4 rereads = 150 new/changed, and 150 + 169 = 319 files.

## Independent resolution of the requested questions

**1. The export is exact.** `selected_actual_material_moment_bound_original` has the original binder list with only `hHC` deleted.
- Its body is a single `exact`, passing `original_HC46_exact` in the `hHC` slot.
- Because it compiled, its conclusion is definitionally the original conclusion: the same `let` block for h, J, c, s, n, Cc, Tc, fc; the same dyadic window for k; the same `≤ 2·selected_actual_analytic_rhs(…, 2e, a)`; and the same center identity.
- It uses no selected-leaf wrapper, and nothing simpler is substituted.
- HC46 enters as the universal contract, applied at `b = selectedF Tc fc` with `hEven := hsplit : c+s = 2h`.

**2. hsmall, hdV and the factor-2 direction.** I traced each part of the derivation.
- **Exponent budget.** `selected_rankloss_exponent` gives `c+s = 2h` and `c + m·s + 2h ≤ 2h(m+2) ≤ 2h² < 2J`, using `m+2 ≤ h` and `A ≥ 1`.
- **Rank loss.** `rankloss_from_exponent` gives `N0·2^(2h−1) ≤ 2^(2J−1)`.
- **The `hsmall` bound.** `hsmall'` rewrites `finrank = 2J`. That is exactly the premise of `grassmann_le_twice_moment`, with d = c, w = s and t = m.
- **The reverse inequality.** Grassmann ≤ 2·matrix follows from `alpha_loss_bound` (I re-derived it: 1−ab ≤ (1−a)+(1−b) and 1−eᵗ ≤ t(1−e)). It is correctly conditional on `hsmall`, and `hsmall` is derived inside the proof, not added as a premise.
- **Center bound.** The free direction, matrix ≤ Grassmann, is used only for the center-mean ≤ β step. It needs only α ≤ 1 and c ≤ n.
- **Result.** None of `hsmall`, `hdV` or `hD` is an export premise. The author's rank-loss guard note is confirmed.

**3. Selector output versus the prescribed instance index (new finding: HIGH, open).** One `m` plays four roles at once: the row count of `I : Instance N m`, the required selector output (`hsel : selector … L = m`), the star arity, and the moment base.
- `selector_unbounded` and `selector_eventually_exists` only prove that *some* output exists. I agree with the author note on that point.
- The selector returns the **maximum** admissible value. Nothing proves that a given m ≥ 256 is ever that maximum.
- The cutoff is supplied by the caller and need not be monotone. If m+1 becomes admissible before m does, an instance with m rows is never selected, and for those instances the theorem holds only vacuously.
- This is not a soundness defect; the statement is honestly conditional. But it blocks readiness, and it raises a fidelity question: should the source row count really be tied to the CMMSA arity?

**4. The untagged-center blanket vacuity claim (complexity packet 3, C1).** Classified as unsupported.
- The obstruction needs `J > (1+18·degree)·m`.
- `degree = algFamily.degree = widthBnd·fitD`, which depends on `120^fifthExp` with `fifthExp := Classical.choose …`. That exponent has no upper bound, so the comparison is not proved at every selected parameter.
- The untagged theorems are unreached anyway: `StarFixedRhoDimensionGuard` reaches only `leafT` and `leafK`. They get no credit, and C1 is closed as out of material scope. The author note is confirmed.

**5. Reached definitions versus source, star and expansion theorems.** On the recorded index, the material root reaches only definitions and types: `matchingStarMass`, `matchingCenterMass`, `MatchesStar`, `SideComplement`, `sideComplement_finrank`, the transported tables, and the graph types `Vertex`, `Dart`, `Edge`, `degree`, `baseRotation`.
- It does **not** reach weighted selection, incidence reweighting, the tagged-to-ordinary acceptance comparison, `cut_expansion` or `crossing_expansion`.
- The bound is therefore for one fixed side complement A and one fixed f. It is not a bound on acceptance. The source/star bridge stays open.

**6. Spectral47.** I independently checked the orbit argument.
- χ_Y(MU) = χ_{YUᵀ}(M), so coefficients are constant on column-space classes.
- Appending keeps only `[Y|0]`.
- The per-class ratio is ∏_{j<i}(2^c−2^j)/(2^{c+s}−2^j) ≤ 2^{−is} ≤ 2^{−i(s−1)}.
- This is consistent with the formal contract being true without premises, which would also make it weaker than manuscript 4.7. **It is reviewer reasoning only: not a machine proof and not a confirmed manuscript match. The contract stays OPEN.**
- Two checks do pass: `basisInv` uses the two-sided-inverse form that `actualLeafIndicator_mul_right_eq` supplies, and `hHeight` uses the same cutoff evaluated at `actualSelectedRho = 1/bOf m`.

**7. Complexitylib, semantics only.** The root reaches seven boundary constants: `algFamily`, `ExpanderFamily.degree`, `degree_pos` and `graph`, `RegGraph`, `rot`, and `relabel`.
- These are data that define the variable and row types of the material carrier. No expansion or spectral theorem content is needed for the statement to mean what it says.
- What the definitions actually are:
  - `RegGraph` is a rotation-map multigraph with loops and parallel edges allowed.
  - `SpectralBound` is a two-sided operator bound on mean-zero functions.
  - Padding uses `padLoops` and folding (`mergedN`), and `famRot 0 = id`.
  - `GraphEdges` keeps loopless representatives only.
- I re-checked these proofs by reading them: the Cheeger, RVW, tower invariant, MergeGen and padding proofs.
- `#print axioms` on the root traverses the full kernel closure, including Complexitylib values such as `exists_finBase` reached through `Classical.choose`. So the standard profile covers that closure for axioms. This is an inference about `#print axioms`, not a supplied enumeration, and it is not body acceptance of the whole external closure.

**8. Complexitylib, computability and runtime (open).**
- No runtime theorem exists.
- The base comes from `Classical.choose` on a counting argument (`ExpanderRandom` proves existence only).
- `fifthExp` and the degree are unbounded and unspecified.
- `rotVal` recurses twice per level with level ≤ 2n, so a naive evaluation takes exponentially many calls.
- The docstrings' "explicit, an algorithm can read" and the `Expander.lean` "no Cheeger or zig-zag" are informal or stale.

## Reconciled findings

| ID | Severity | Declarations | Disposition | Evidence | Remaining action |
|---|---|---|---|---|---|
| I1 | Resolved | `…material_moment_bound_original` | Removes only hHC; conclusion and guards are exact | Export body, the `exact` call, 173-root stdout | Remove stale comment ("not compiled") |
| I2 | Resolved | `selected_rankloss_exponent`, `rankloss_from_exponent`, `grassmann_le_twice_moment`, `alpha_loss_bound` | hsmall, hdV and hD are derived; factor-2 direction is correct | §2 | — |
| I3 | **HIGH (open, readiness)** | `hsel`, `Instance N m`, `selector_spec` | Prescribed m is not shown to be a selector output; possible vacuity for some m and some cutoffs | §3 | Prove every relevant m is selected for some L, or decouple instance size from arity; manuscript check |
| I4 | HIGH → resolved (out of scope) | Untagged `selected_*` guards, `rows_length_le` | Blanket vacuity unsupported; unreached; no credit | §4 | Explicit degree comparison only if these are ever credited |
| I5 | Medium (open) | `Spectral47ExactContract` | Remains a premise; sketch is consistent but not machine-checked | §6 | Machine proof or keep as premise; 4.7 fidelity audit |
| I6 | Resolved | Tc, fc, Cc, transported tables, A | Same objects throughout; one fixed A and one fixed f | Material body | Note: not an acceptance bound |
| I7 | Resolved | `actualLeafIndicator_mul_right_eq`, `selected_spectral_parameters` | Inverse form and cutoff/ρ identity match | §6 | — |
| I8 | Medium (open) | Source/star bridge declarations | Unreached; ordinary-density and weighted-selection results are compile-only | Reached-constant index | source/star/robust8S gate |
| I9 | Medium (open) | `selected_actual_analytic_rhs`, `hfail`, `a` | Raw RHS. The i = 0 term alone is ≥ 2^m·β^{1−m/k}·(2e)^{m(k−2)/k}; i ≥ 1 adds 2^{500i²km}. The author's a* algebra checks: f = (1+m/2)·A0·a*^m | §8 inputs | Numeric NO; useful e; control of B |
| I10 | Medium (open) | Complexitylib computable definitions; `blocks` | No runtime or encoding theorem; J is doubly exponential; degree unbounded | §8 | encoded reduction / runtime gate |
| I11 | Info | Complexitylib semantics | Reached as data only; proof closure is axiom-standard (inference) | §7 | Enumerate external closure only if crediting by name |
| I12 | Low | Banners in export, MatrixGrassmannIdentity, PortCycleReplacement, SamplerParameters, FixedPortCycleFamily, CoveringSpan/TV; `Expander.lean` | Stale; no weight either way | Bodies | Clean up before render |
| I13 | Low (open) | `#print axioms` inside consumed StarQuestionSupport and StarSpanIntersection; linter suppressions | Build-log info output; zero owned warnings ≠ zero total warnings | Bodies | Warning/log disposition |
| I14 | Info | `respectTransparency false` (CoordinateMassBridge, MatrixGrassmannIdentity) | Affects the elaborator only | — | Note for replay |
| I15 | Resolved | Packet-1 PA1-06 (`copies` vs m) | `copies` is the tagged source multiplicity; the real coupling is I3 | — | — |
| I16 | Out of scope | Upstream seven-target custody | Selected upstream targets only; no CMMSA bridge; post-audit pending | Receipt | Bridges and post-audit |

**Missing bodies or profiles:** none were skipped. Not available:
- per-declaration profiles for unreached declarations;
- an enumeration of the external closure;
- manuscript texts;
- total-warning logs and a fresh checkout.

## Safe conditional claim

Under pinned kernel and Init/Mathlib/Batteries trust, the qualified native receipts, the Complexitylib bodies as reached data, and identity-verified reuse of the 169 prior bodies:

> For every I, copies, U, A, C, T, f, base and cutoff satisfying `hsel`, `1 ≤ samplerA`, `r < leafT + leafK`, `0 ≤ e`, `hfail(e)` on the same coordinate leaf table, `Spectral47ExactContract cutoff`, and `0 < a`, the following holds with standard axioms and **no hHC premise**:
> - there is a dyadic k with 4m ≤ k < 8m;
> - the ordinary-star matching mass on the fixed side complement A is ≤ 2·`selected_actual_analytic_rhs`(Cc, Tc, fc, r, k, 2e, a);
> - the center mass equals the exact Grassmann fraction.

**Not claimed:**
- that all premises can be satisfied together (I3), or that Spectral47 is proved;
- a useful e, `hfail`, a, or numeric NO;
- source/star/robust8S, acceptance bounds, or expansion on the trace;
- encoded reduction, runtime, learning, or explicitness of any expander;
- standard profiles for unreached declarations, or acceptance of the whole external closure;
- CMMSA bridges from upstream builds;
- zero total warnings, a fresh checkout, novelty, citations, render, the final providers, or manuscript acceptance.

## Remaining to-do

1. **I3:** prove that every relevant instance size is a selector output (for monotone or specified cutoffs), or restructure so arity is chosen independently of the instance row count; confirm against the manuscript.
2. **Spectral47:** machine-check the orbit argument or keep it as a premise; audit fidelity to manuscript 4.7.
3. **Numeric:** control B, find a useful e satisfying `hfail` and a choice of a, compare 2·RHS against the NO threshold.
4. **Source/star bridge:** tagged acceptance → ordinary density → selected f, all on the trace; close robust8S (`AllAmbientInverse`).
5. **Encoded reduction and runtime:** explicit bounds on the expander degree and table computation; the size of the doubly exponential J.
6. **Upstream:** independent post-audit of the seven-target custody, then the CMMSA consumer bridges.
7. **Hygiene:** warning and info-log disposition, removal of stale banners, fresh-checkout replay.
8. **Manuscript and release:** manuscript fidelity (HC4.6, A7–A22, DR6, 4.7, the CMMSA coupling), novelty, citations, render, final full-scope providers.
