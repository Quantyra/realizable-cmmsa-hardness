# SourceSize / dyadic Spectral47 discharge: proof-adversarial review (not final acceptance)

**Bottom line:** the two new theorems follow mathematically, and I found no wrong argument order, dropped premise or altered conclusion, and no legacy material consumer. I do expect the file not to parse as written (P1, below). The two new candidate files are uncompiled, so reading them here is not kernel evidence. There is no overall GO.

I used no tools, Lean/Lake, writes or subagents, and I recomputed no SHA-256 values; every hash below is copied from the packet.

## Scope and how coverage was split

**Fresh full review (the acceptance scope):**
- `ActualSelectedComplementSourceSizeSpectralApplication.lean` (5BF441CD…)
- `…SourceSizeSpectralApplicationChecks.lean` (448189FE…)
- The static derivation JSON
- How both compose with their actual consumers

**Re-read only for this composition, under reuse:**
- The captured bridge (022E14E6…).
- The two consumers it wraps: SourceSizeOriginalApplication (22DE415F…) and ManuscriptDyadic (AF3E380A…). Both match the Full100 native identities.
- The SourceSize `Spectral47ExactContract` and `selected_actual_material_moment_bound`.
- The Full101 `spectral47_exact_contract_inhabitant`.

**Reuse only (41 prior bodies):** the 33 earlier bodies and the 8 bodies added last round were not freshly reviewed in full. Their semantics rest on the three earlier review rounds. I do not claim coverage of all 340 or all 327 sources.

## Composition checks

**Theorem 1: `…_original_spectral_discharged`**
- **Target.** It calls `ActualSelectedComplementSourceSizeOriginalApplication.selected_actual_material_moment_bound_original`, fully qualified. That consumer takes `Instance N rows`, so it is the SourceSize lane, not the legacy `Instance N m` lane.
- **Argument order.** The consumer's explicit order is I, copies, U, A, C, T, f, base, sourceHeightCutoff, hsel, hA, r, hrd, e, he, hfail, **hSpectral**, a, ha. The candidate supplies exactly that order, with the bridged inhabitant in the hSpectral slot. The implicits {N rows m L samplerA} are inferred from I, U and hsel.
- **HC46.** The consumer's own body passes `original_HC46_exact` into the SourceSize `selected_actual_material_moment_bound`. The candidate does not touch HC46.

**Theorem 2: `…_at_dyadic_exponent_spectral_discharged`**
- **Target.** It calls `ManuscriptDyadicMoment.selected_actual_material_moment_bound_original_at_dyadic_exponent`.
- **Argument order.** The consumer's order is …hfail, **hSpectral**, a, ha, hkDyadic, hkm, and the candidate matches it. The implicit k is fixed by hkDyadic, hkm and the goal. The consumer's body supplies `original_HC46_exact`.

**The Spectral47 term.** The candidate passes `(SourceSizeContractBridge.spectral47_contract_iff cutoff).mp (spectral47_exact_contract_inhabitant cutoff)`.
- The inhabitant's type is the **legacy** contract: its file opens `ActualSelectedComplementAnalyticMoment`.
- `.mp` of the bridge (legacy ↔ SourceSize) gives the SourceSize contract, which is the right direction.
- The bridge is `Iff.rfl` and native-qualified in Full100.

**Premises and shared objects.**
- The common I, copies, U, A, C, T and f are threaded unchanged. Cc, Tc and fc are rebuilt from them inside the consumers' `let` blocks.
- The candidate's text is identical to each consumer apart from removing `hSpectral`. That covers: rows kept independent of the leaf arity m; m fixed through `hsel` and `matchingStarMass (m := m)`; and the guards `hsel`, `hA : 1 ≤ samplerA`, `hrd`, `e ≥ 0`, `hfail` (failed-zoom on the same coordinate leaf table), `a > 0`, plus `hkDyadic` and `4m ≤ k` for the dyadic theorem.
- Height, parity, ρ, the c/s split and the dimension guard (`hdim`) are not caller premises. The consumers derive them internally from `selected_spectral_parameters` and h² < J; that body was not supplied.

**Conclusions.**
- Fixed-window theorem: ∃ k q with k = 2^q, 4m ≤ k < 8m, mass ≤ 2·rhs, and the center identity.
- Dyadic theorem: the same two conjuncts with k chosen by the caller. The `let … fc := …;` form is copied from the native consumer.
- Both match their consumers exactly.

**Namespaces.** The candidate opens the same namespaces as SourceSizeOriginalApplication, except the HC46 inhabitant namespace, which the candidate does not need.
- The legacy module enters the environment transitively through the Full101 inhabitant, but its namespace is never opened.
- So `selected_actual_source_dimension_bound`, `selected_actual_analytic_rhs` and `analyticSourceHeightFloor` resolve to the SourceSize and parameter declarations, not their legacy namesakes.

**No legacy material consumer is used.**

**Mathematical implication.** Given the inhabitant, each new theorem is modus ponens. Whether the result is sound therefore rests entirely on the inhabitant: the reused Full101 fixed-image ratio argument, which three earlier rounds judged sufficient. It does not depend on these two files.

## Findings

| # | Severity | Kind | Evidence | Disposition and action |
|---|---|---|---|---|
| **P1** | **HIGH (probably blocks compilation)** | Elaboration/parse risk | Four places break a dotted identifier across a newline right after the dot: theorem 1 and theorem 2 (`…ExactInhabitant.⏎ spectral47_exact_contract_inhabitant`), and twice in the Checks `example` (`…SourceSizeAnalyticMoment.⏎ Spectral47ExactContract` and `…ExactInhabitant.⏎ spectral47_…`). I believe Lean 4's identifier lexer does not continue past a `.` followed by whitespace. If so, the leftover `.` parses as a field projection that fails its no-whitespace check, giving a parse error. Mathematically harmless. | Join each identifier onto one line, or `open` the namespace, in a new candidate with new hashes and re-run the static type derivation. Then compile. If you would rather get the compiler's diagnostic first, launch as-is and repair afterwards. Do not edit frozen Full101 either way. |
| P2 | HIGH | Native dependency | The candidate imports `ActualFiniteAppendSpectral47ExactInhabitant`, so it cannot compile until frozen Full101 (11 files, uncompiled) compiles as captured. The earlier rounds' A1 risks (decidability/filter, cast/HEq, `field_simp`) and possible unused-binder warnings in the inhabitant are still there. | Renew GCP authentication. Compile Full101 unchanged and collect its real diagnostics. Only then compile the candidate and its Checks. |
| P3 | LOW–MEDIUM | Elaboration | The stated types contain `if centerMatchBit … then` and `Fintype` instances, under `attribute [local instance] Classical.propDecidable`. The consumers elaborated in the same instance context, so `exact` should match their syntax exactly. A divergence between the two contexts would be a subsingleton-but-not-defeq mismatch. | Confirm at compile time. The fallback is to state the types via `@`-application of the consumer instead of copying the text. |
| P4 | MEDIUM | Claims boundary | Only `hSpectral` is removed. The callers still keep the selector, failed-zoom, `hrd`, `hA`, `a > 0` and dyadic premises. The conclusion is still `2 · selected_actual_analytic_rhs`, which carries the weaker `2^{−i(s−1)} + 3·2^{i−n}` factors and the unreduced high-level energy sums. Neither theorem certifies the exact eigenvalue, 𝒢/Φ or the adjoint. The fixed window 4m ≤ k < 8m is not the manuscript route (that needs P ≥ mT); only the dyadic theorem fits it. | State this as "the actual SourceSize consumers with Spectral47 and HC46 discharged". Do not call it completion of the source, table, runtime or scalar steps. |
| P5 | MEDIUM | Coverage | Load-bearing bodies that have never been supplied to any review round: `ActualBinaryMatrixHC46OriginalExactInhabitant` (`original_HC46_exact` and its axiom profile); `ActualSelectedComplementSourceSizeAppendMoment` (mass bound, center identity, `hsmall`); `ActualSelectedSpectralParameters` (source of the height/ρ/split guards); `ActualLeafLabelRankImageAlignment`; `ActualComplementCoordinateMassBridge`; and `selector`, `SamplerParameters` and `ActualStarFixedRhoDimensionGuard`. Full100 native GREEN gives them kernel type-correctness as captured, but reuse of earlier body reviews cannot cover them because none of those reviews saw them. | Supply them for independent body review. |
| P6 | LOW | Axiom checks | The Checks file prints axioms only for the two new theorems. The `example` gets type-checked but has no axiom output. | Also `#print axioms` for `spectral47_exact_contract_inhabitant`, `original_HC46_exact` and the two consumers, so the profile can be attributed. Require exactly {propext, Classical.choice, Quot.sound} and no `sorryAx`. |
| P7 | LOW | Evidence tier | The derivation's `exact_type_reconstruction: true` and its type hashes are textual; the hashing method is unspecified. | Treat as static evidence only. Kernel elaboration of the candidate is what confirms the types. |
| P8 | INFO | Design | Passing the legacy inhabitant directly would also type-check, since the bridge is `Iff.rfl`. Going through the explicit bridge is preferable and traceable. | No action. |

## What reuse can and cannot cover

**Reuse covers:**
- The mathematical sufficiency of the inhabitant (three earlier rounds).
- The M1 operator and source-shape crosswalk (last round).
- The signatures of the wrapped SourceSize and dyadic consumers, whose identities match Full100 native.

**Reuse cannot cover:**
- The P5 bodies listed above.
- Native compilation of Full101, the exact-energy candidate, the earlier selected-leaf application, and these two new files.
- The consumption trace. The native report still shows `consumption_trace_complete: false`.

## Verdicts

| Question | Verdict |
|---|---|
| Mathematical implication | Valid: modus ponens on a reused inhabitant judged sufficient |
| Composition (argument order, namespaces, rows/m, guards, conclusions, HC46 provenance) | Correct by reading |
| Native readiness | Not ready: P1 likely parse defect, P2 Full101 dependency |
| Manuscript / final readiness | Not ready; still open: exact eigenvalue/operator, scalar/source/runtime/upstream debt, R14 HIGH, manuscript/citation/publication gates |
| Overall | No GO |

## Remaining to-do list

1. Fix P1 in a new, hashed candidate: put each dotted identifier on one line and re-run the static type derivation. Or launch as-is and repair from the compiler's diagnostic.
2. Renew GCP authentication. Compile frozen Full101 unchanged first, then the exact-energy candidate and its Checks, the selected-leaf application and its Checks, and this candidate and its Checks. Collect real warnings and axiom profiles.
3. Extend the Checks file with `#print axioms` for the inhabitant, `original_HC46_exact` and both consumers (P6). Require no `sorryAx`.
4. Run the consumption trace: confirm the kernel terms reference the SourceSize consumers, the bridge, the Full101 inhabitant and `original_HC46_exact`, and no legacy material consumer.
5. Supply and review the P5 bodies.
6. Separately: native exact eigenvalue / 𝒢 / Φ / adjoint and the product identity (i ≤ d guard, explicit zero branch); scalar caller reductions; binding the manuscript's P to the dyadic k; and checking J (`SamplerParameters.blocks`) against the manuscript's choice of J.
7. Keep open: numeric NO; source/star/robust8S/pre-draw witnesses; sampling, encoded reduction, runtime and learning; upstream transports; R14 HIGH; warnings, fresh-checkout and custody replay; novelty, citations and PDF; final provider QA; publication. No overall GO.
