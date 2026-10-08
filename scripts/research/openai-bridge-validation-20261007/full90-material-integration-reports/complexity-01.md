# Full90 whole-material integration review (complexity lens)

## Verdicts

These are three separate verdicts on three separate scopes.

| Scope | Verdict |
|---|---|
| **Material statement and native integration.** The conditional root `selected_actual_material_moment_bound_original`, as stated. | **GO‑WITH‑NOTES.** No required body is skipped. No HIGH finding against this scope is unresolved. |
| **Unconditional material readiness.** Useful, discharged premises for a real source instance. | **INCOMPLETE. No readiness supported.** Spectral47 is open. So are inhabiting the guards jointly at a fixed instance, a useful e for `hfail`, and numeric NO. One HIGH finding sits on the already‑open reduction/runtime gate (R14). |
| **Manuscript** | **Not issued.** There is no manuscript acceptance. Fidelity, render, novelty, citations and the final provider gates are all open. |

**How I reviewed.** I used no tools, wrote nothing, did not run Lean or Lake, and recomputed no hashes. Native, compiler and custody facts are taken from the supplied receipts. I treated the author reconciliation notes as hypotheses and re‑checked each one against the bodies below.

## Coverage

- **Complete bodies in this integration: 63 supplied, 63 inspected, 0 skipped.**
  - 5 material‑critical project files: OriginalApplication, AnalyticMoment, AppendMoment, OriginalExactInhabitant and LeafLabelRankImageAlignment.
  - 35 other reached project modules: AppendFourier…, SamplingBounds, both Cmmsa modules, CoordinateMassBridge, EqualityCloud, Finite3Lin, FiniteLaw, FiniteMomentLp, AppendOperator, BinaryMatrixMoment, GraphEdges, OccurrenceAllocation, both OrdinaryStar modules, RankImageInvariance, RhsFunctional, SelectedSpectral, DimensionGuard, QuestionSupport, SpanIntersection, TaggedComplementIncidence, the density bridge, TaggedConcreteStarLaw, FixedCenterGeometry, FixedTableAcceptance, OrderedSampleNonempty, CoveringSpan, CoveringTV, EqualityGadget, FixedPortCycleFamily, MatrixGrassmannIdentity, PortCycleReplacement, SamplerParameters and TaggedFinite3Lin.
  - That is 40 project modules, all pinned `transitively_consumed: true`, plus the 23 Complexitylib modules.
- **Reports read:** all 15 fresh packet reports; the 30 prior reports and 3 prior syntheses; and 6 author receipts.
- **Corpus coverage:** 169 bodies reused, strictly under the verified identity audit (7251 shared nodes; compiler and package preserved). 150 new or changed bodies were reviewed across 5 packets × 3 lenses, plus 4 critical re‑reads and 23 Complexitylib files. That makes 177 unique files per lens, matching the snapshot. Together this covers all 319 files.
- **Not reread:** I did not reread the 169 reused bodies in this pass, and I make no claim that I did.

## Independent resolution of the specific questions

**1. Is `hsmall`/`hdV`/`hD` discharged, and which way does the factor of 2 point? Resolved from source.**
- **Derivation chain:** `selected_actual_append_moment` gets `hdim`, `hD` and `hsmall` from these steps:
  - `selector_spec` gives `m+2 ≤ h`;
  - `numerator_lt_blocks` with `hA` gives `h² < J`;
  - `selected_rankloss_exponent` gives `c+s = 2h` and `c+ms+2h ≤ 2h(m+2) ≤ 2h² ≤ 2J`;
  - `rankloss_from_exponent` gives `N₀ = c+ms ≤ 2^{N₀}` and `N₀+2h−1 ≤ 2J−1`, so the rank‑loss term is at most 1/2;
  - `hsmall'` then rewrites the coordinate finrank to `2J`.
- **No extra premise:** the export adds no hsmall‑ or hdV‑style premise.
- **Direction:** the star‑mass bound uses the reverse direction, `grassmann_le_twice_moment` (Grassmann ≤ 2·matrix). That direction needs α ≥ 1/2, which comes from `alpha_loss_bound` plus the derived `hsmall`. The center bound uses the free direction (matrix ≤ Grassmann, via `alpha_bounds`, α ≤ 1, at t = 0 with guard `c ≤ n`). Both directions are applied correctly. The star copy count k equals the selector m in both the `hsmall` check and the star law.

**2. Selector existential output versus the prescribed instance index: partly resolved, partly open.**
- **What holds:** the reconciliation note is right as source reasoning. Instantiating `selector_unbounded` at `S j = max(analyticSourceHeightFloor base cutoff j)(j+2)`, the export's exact floor, gives, for all large L, *some* output m ≥ 256 that is admissible. So a fast total cutoff does not make `hsel` uninhabitable.
- **What is open:** the m in `hsel` is the *same* binder as the m in `I : Instance N m`. It is used at the same time as:
  - the row count of the source instance;
  - the selector index;
  - the star arity / moment exponent;
  - the parameter inside `bOf m` and `leafK`.
- No theorem says that `selector(·, L) = m` holds for a *prescribed* m.
  - The gate `bOf n ≤ √log₂L` pins the selector at or below m only while √log₂L < 4000(m+1)².
  - Inside that window m is admissible only if `sourceHMin m ≤ hBlock ≈ ½log₂L`.
  - With a fast cutoff, the selector can skip m. For strictly increasing floors it plausibly hits every m, but that is unproven: per‑m rounding of `hBlock` and the divisibility conditions interfere.

**3. Arbitrary, classically chosen degree versus the claimed blanket vacuity of the untagged center.**
- **Disposition:** I downgrade complexity‑03's C1 from HIGH to *unsupported as stated*.
- **What vacuity would need:** the obstruction is `J > |RowId|`, which needs `J > (1+18·FixedPortCycleFamily.degree)·m`.
- **Why that is not established:**
  - `degree = algFamily.degree = (2·d⁴+1)·d²`, where `d = algBase.deg` and `algBase = Classical.choose exists_finBase`.
  - `Classical.choose` does not reduce to the witness, so d is an unknown fixed constant with no upper bound.
  - With J ≥ 2^{2^{h²}} and h ≥ m+2, vacuity follows only for m beyond a threshold that depends on that unknown constant. It does not follow for all m ≥ 256.
- **No material impact:** the trace shows `ActualStarFixedRhoDimensionGuard` reaches only `leafT`/`leafK`. The untagged selected guards are unreached. They must still never be cited as evidence about the source or the star.

**4. Definitions actually reached versus source, star and expansion theorems.**
- **Index cross‑check:** the reached‑constant index agrees with the bodies:
  - OrdinaryStarWeightedSelection: only `matchingStarMass`/`matchingCenterMass`.
  - TaggedComplementIncidence: `SideComplement` and `sideComplement_finrank`.
  - DensityBridge: the transported tables.
  - SamplingBounds: `gaussian_pos`.
  - FixedPortCycleFamily: `degree`/`base`/`labels`, with no `cut_expansion`.
  - PortCycleReplacement: `Port`/`rotation`.
  - GraphEdges: just enough to type `Edge`.
- **Not reached:** the weighted selection, incidence reweighting, the tagged‑to‑ordinary acceptance comparison, Chernoff/KMS covering, and the expansion theorems all lack fresh profiles and get **no credit**.
- **Semantic dependence:** the material statement depends on the concrete `algFamily` rotation only through the *type* of `I`, namely which edges exist. It does not depend on any expansion property.

**5. Is the exported statement exact? Resolved.**
- **Text match:** the export's binders equal the original's minus `hHC`. Its conclusion matches the original token for token: same `let` block, same coordinate tables (`selectedCoordinate*Table`, `coordinateFunctional`), same `Tc`/`fc` in `hfail`, the 2e/a right‑hand side, and the center identity.
- **Proof:** the body is a single `exact … original_HC46_exact …`. The kernel has checked definitional equality, and `CoordAmbient` and `CoordinateAmbient` are both `Fin _ → ZMod 2`.
- **HC46 route:** HC46 is applied through the universal contract with `hEven := hsplit`. It does not go through the selected‑leaf wrapper.
- **Guards retained:** `hsel`, `hA`, `hrd` (`r < c+s`), `he`, `hfail`, `hSpectral` and `ha`. The profile is {propext, Classical.choice, Quot.sound}.

## Reconciled findings

| ID | Source | Declarations | Severity (old → now) | Disposition and evidence | Remaining action |
|---|---|---|---|---|---|
| R1 | PA1‑01/03; packets 2–5 "export not visible" | `selected_actual_material_moment_bound_original` | Medium → **resolved** | Exactly `hHC` removed; same conclusion and guards; kernel `exact`; standard profile (Q5 above) | None |
| R2 | C3 (cx‑02), N3 (nc‑02), PA2‑3, P5‑6 | `selected_actual_append_moment`, `rankloss_from_exponent`, `grassmann_le_twice_moment` | Medium → **resolved** | Derived, not assumed; both factor‑2 directions correct (Q1) | None |
| R3 | PA1‑04, cx‑01 P2, prior F2/F3 | `Spectral47ExactContract` | Medium, **open** | I re‑derived the orbit argument independently, and it is plausible:<br>• `basisInv` makes F̂ constant on column‑space orbits;<br>• the append average keeps only `[Y|0]`;<br>• the energy ratio per orbit is ∏(2^c−2^j)/(2^{c+s}−2^j) ≤ 2^{−is} ≤ 2^{−i(s−1)}.<br>This is **not** a machine proof and **not** a verified match to the manuscript. If it holds, the encoded contract is weaker than Spectral 4.7. | Machine‑check the argument or keep it as an explicit premise; manuscript‑fidelity check |
| R4 | C4 (cx‑03), N3 (nc‑03) | `selector_unbounded`, `analyticSourceHeightFloor`, `hsel` | Medium → **partly resolved** | An output exists for every total floor (Q2). L₀ is not effective. | Theorem hitting a prescribed index; effective L₀ |
| R5 | new | the shared m in `Instance N m` / `hsel` / `matchingStarMass (m:=m)` / `bOf m` | **Medium, open (fidelity)** | Source row count = selector index = star arity. Applicability to a fixed source instance needs `selector(L) = m`. | Manuscript check of this coupling; joint inhabitance |
| R6 | C1 (cx‑03) | untagged `selected_*` guards, `rows_length_le` | HIGH → **Info / non‑claim** | Universal vacuity unsupported (unknown classical degree; Q3). Unreached by the root. | Never cite these lemmas |
| R7 | C2/N1/N2, P3‑2 | `labelledTransverseLaw`, the Rel‑acceptance lemmas | Medium, **retained non‑claim** | Positivity comes from uniformly drawn labels; the accepted rank‑good event is empty. Unreached. | Never cite as soundness |
| R8 | P3‑1, C5, N9 (nc‑03) | weighted selection, incidence, density bridge | Medium → **resolved (scope)** | The index shows only definitions are reached; these theorems have compile evidence only | No credit |
| R9 | PA4‑02, C4‑4, CX‑05, P5‑1, N7 | `algFamily`, `ExpanderFamily.graph`, `RegGraph.relabel` | Medium → **partly resolved** | 7 boundary constants; `algFamily` is a closed constant, not an assumed `ExpanderFamily` premise (Complexitylib audit below) | Expansion and hardness bridge stays open |
| R10 | PA1‑05, P3, N2, N4 | `selected_actual_analytic_rhs` | Medium, **open** | My uncertified scale analysis:<br>• the target selection scale is ~2^{−ms}·β·ε, which forces a ≲ 2^{−s};<br>• the weighted high‑energy term is then useful only for levels i ≳ 3, so r ≥ 2;<br>• the low HC term then forces e ≲ 2^{−Ω(r²k)} with k ≥ 4m;<br>• whether `hfail` can hold at that e (leaf dimension 2h ≫ m²) is the real open question.<br>The a* optimization in the reconciliation note is algebra only. | Certified numeric comparison |
| R11 | P2‑4, C1 (cx‑02) | `hn_handoff`, `Admissible` | Low | Only the definitions are reached; `16 ∣ gapRoot` is not exported | Prove before any HN use |
| R12 | N5 (nc‑02), C4 (cx‑02) | `E1_not_75/150/225` | Medium, **open (fidelity)** | The formal exponents 47/127/216 differ from the manuscript's. Unreached. | Manuscript audit |
| R13 | PA4‑06 / C4‑1 | the force theorems' `hp`/`hq` m | Low | m is the instance m. Unreached. | Fidelity |
| R14 | new; sharpens C5‑1 / P5‑6 | `hBlock`, `blocks` | **HIGH for the reduction/runtime gate** (outside the material‑statement scope) | `hBlock L m ≈ ½log₂L`, so J = 2^{2^{A h²}} ≈ 2^{L^{(log L)/4}}. Tables over the Grassmannians of a 2J‑dimensional ambient are therefore nowhere near poly(L) and cannot be materialized; this follows directly from the definitions. Does not affect the conditional theorem's truth. | The encoded reduction must be implicit, or the parameters reconciled |
| R15 | N8, C6, P3‑5, P2‑5 | linter suppression in `LeafRejectionUnion`/`ActualStarAcceptance`; `#print axioms` lines inside library modules | Low, **open** | Zero owned warnings ≠ zero total warnings; part of it comes from suppression | Warning and log disposition |
| R16 | P5‑3, PA4‑03, N1 (nc‑01) | stale "UNCOMPILED"/"not compiled" banners (including consumed modules and the export comment) | Low | No evidential weight either way | Clean up before render |
| R17 | prior R4–R6 | `PseudorandomExact` | **Boundary retained** | One‑sided, nominal exact budget, factor 2e, requires `r < d` | Never describe as two‑sided |
| R18 | P4 (cx‑01) | `hfail` at e ≥ 1/2 | Info | Trivially satisfiable; the conclusion is then weak | Part of R10 |
| R19 | upstream receipt | the 7 OAI selected targets | Info | Two copies with matching hashes, profiles standard. The receipt itself says independent post‑audit is pending and there is no CMMSA bridge. | Post‑audit; build the bridges |

## Complexitylib (audited separately)

**Mathematics: no defect found.** I spot‑re‑derived these:
- `SpectralBound` is a two‑sided squared contraction on mean‑zero functions.
- Cheeger, lazy form: Dirichlet ≥ h²d‖f‖² gives ⟨f, Af⟩ ≤ (1−h²/2)‖f‖², so the lazy bound is 1−h²/4.
- PermGraph: h = 1/(2·10·30).
- ZigZag tower: 4/25 + 5/25 + 1/25 = 2/5.
- Merge at width 3: 0.16 + 0.14 + 1/3 ≤ 0.64.
- Padding: 1 − (9/25)α ≤ 1 − 27/(25W).
- `famRot 0 = id` (vacuous for an empty graph).
- `relabel` keeps vertex values.

**Representation used by the material statement:** it reaches `algFamily`, `ExpanderFamily.degree`, `degree_pos` and `graph`, plus `RegGraph`, `rot` and `relabel`. These fix only the rotation, so which edges and ports the instance has. `ExpanderFamily` is genuinely inhabited by `randExpander` and `algFamily`. It is not an assumed interface.

**Axioms:** the root's standard profile, read with `#print axioms` semantics (which traverse definition values), implies the reached Complexitylib closure contains no non‑standard axiom. That is axiom freedom only. It is not proof review, and it does not expand the recorded boundary graph.

**Computability and runtime: none established.**
- `algBase` is a `Classical.choose` over a choice‑based `randExpander`.
- `famRotVal` is noncomputable, and the degree is an unbounded unknown constant.
- `NumEnc.ofFintype` uses an arbitrary numbering.
- The "explicit / an algorithm can read" docstrings are not theorems, and the `Expander.lean` docstring is stale.
- `ExpanderRandom` proves existence only, not a high‑probability sampler.
- The gap constants are tiny or unspecified.
- Encoded reduction and runtime stay open.

## Missing bodies or profiles

- **Bodies:** none missing in the 319‑file corpus or the 23‑module Complexitylib context.
- **Profiles:** none of the unreached theorems listed in R6–R8, R12 and R13 has a fresh profile.
- **Not provided:**
  - per‑constant enumeration of the external (Mathlib) closure;
  - any proof inhabiting Spectral47;
  - a prescribed‑index selector theorem;
  - a joint‑inhabitance witness for `I`/`copies`/`U`/`A`/`hfail`;
  - a certified numeric‑NO comparison.

## Safe conditional claim

> Assume:
> - the pinned kernel and Init/Mathlib/Batteries trust;
> - the qualified Full90 native receipts: 173 standard root profiles including the export, 319 pins, seven stage exits of 0, terminated custody;
> - identity‑eligible reuse of the 169 prior bodies.
>
> Then `selected_actual_material_moment_bound_original` proves the following, with no HC46 premise. Take any `I : Instance N m`, any copies, U, A, C, T and f. Suppose the selector at the export's analytic floor returns this same m, and that `1 ≤ samplerA`, `r < leafT+leafK`, `0 ≤ e`, the failed‑zoom bound `hfail(e)` on the same coordinate leaf table, `Spectral47ExactContract(sourceHeightCutoff)`, and `a > 0` all hold. Then:
> - there is a dyadic k with 4m ≤ k < 8m such that the transported matching‑star mass is at most `2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)`;
> - the matching‑center mass equals the exact Grassmann center fraction.
>
> All finite sampling guards (`hdim`, `hD`, `hsmall`) are derived internally.

**Not claimed:**
- Spectral47 (despite R3);
- that the selector hits a prescribed m, or joint inhabitance;
- a useful e, `hfail`, a, or numeric NO;
- source, star or robust8S;
- graph expansion on the trace, or any computable or polynomial‑time expander;
- encoded reduction, runtime or learning;
- the CMMSA upstream bridges;
- zero total warnings, or a fresh checkout;
- manuscript fidelity, render, novelty or citations;
- final providers;
- acceptance.

## Remaining to‑do

1. Machine‑check the Spectral47 orbit argument (R3), which could remove `hSpectral`, or keep the premise explicit. Check fidelity against manuscript Spectral 4.7.
2. Prove a prescribed‑index selector theorem with an effective L₀, and settle the coupling of the instance's m with the selector's m against the manuscript (R4, R5).
3. Build a joint‑inhabitance witness: the actual source I, copies large enough for `TaggedGoodU`, U, A, C, T and f.
4. Do a certified numeric‑NO comparison (R10): choose r ≥ 2, a and e; prove `hfail` at that e.
5. Reconcile the reduction and runtime with J ≈ 2^{L^{(log L)/4}} (R14), and give the CMMSA encoded reduction implicitly. Complete source/star/robust8S, including `AllAmbientInverse`, and learning.
6. Prove the expansion and hardness bridge from `algFamily` to the source instance (R9). Add no runtime claim based on Complexitylib.
7. Finish the independent post‑audit of the upstream seven‑target receipt, then build the CMMSA bridges (R19).
8. Dispose of warnings and logs, including the linter suppression and in‑library `#print axioms` (R15). Remove stale banners (R16). Replay from a fresh checkout.
9. Manuscript fidelity: E1 exponents, constants, the `PseudorandomExact` semantics, the m couplings (R12, R13, R17). Then render, novelty, citations and the final full‑scope providers.
