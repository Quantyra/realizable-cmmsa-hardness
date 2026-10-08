# Full90 material integration review (proof-adversarial lens)

## Verdicts

| Scope | Verdict |
|---|---|
| **Material statement and native integration**: the exported `selected_actual_material_moment_bound_original`, its reached closure, all 63 bodies supplied here, and identity-eligible reuse | **GO-WITH-NOTES** |
| **Unconditional material readiness** | **INCOMPLETE.** Several premises are not shown jointly inhabitable with useful parameters: `hSpectral`, `hsel` at the fixed instance index, `hfail` with a useful `e`, and the numeric RHS. |
| **Manuscript** | **No verdict.** Not accepted. |

**Coverage**
- All 63 complete bodies were inspected and none skipped: 5 changed or critical project bodies, 35 other project bodies, and 23 Complexitylib bodies. The 35 project modules are AppendFourierCrossLevelOrthogonality through TaggedFinite3LinSource, as listed in the input.
- I also read all 15 fresh reports, the 27 prior packet reports and the 3 prior syntheses.
- Coverage of all 319 project files rests on 169 reused identities plus 150 new or changed bodies reviewed across the 5 packets. I did not re-read the 169 reused bodies, and nothing here claims I did.
- No HIGH finding remains unresolved in this scope, and no required body was skipped.

**Limits of method**
- I used no tools and ran no Lean or Lake.
- Native, compiler and custody facts come from the supplied receipts.
- Author reconciliation notes were treated as hypotheses. Each one was re-derived from source below.

## Core checks, re-derived from source

**Export fidelity**
- The binders are the original binders with `hHC` deleted. The body is a single `exact … original_HC46_exact hSpectral a ha`, so the kernel has accepted the conclusion as definitionally the original.
- The objects are the same throughout:
  - the same I/copies/U/A/C/T/f;
  - `Tc = selectedCoordinateLeafTable`, used in `hfail`, in the PR premise and in the moment;
  - the same `Cc`/`fc` in the center identity.
- HC46 is applied through the universal contract with `hEven := hsplit : c+s = 2h`. The selected-leaf wrapper is not used.
- The reached-constant JSON confirms that the root reaches `original_HC46_exact` and the A22/A18/A21 chain.

**`hsmall` and `hdV` are discharged, not assumed**
- `selected_rankloss_exponent` derives `c+s = 2h` and `c + m·s + 2h ≤ 2h(m+2) ≤ 2h² < 2J`. It uses `m+2 ≤ h` from the selector floor, and `A·h² < blocks` with `A ≥ 1`.
- `rankloss_from_exponent` gives `N₀·2^{2h−1}/2^{2J} ≤ ½`. I re-checked this using `N₀ ≤ 2^{N₀}` and `N₀ + 2h − 1 ≤ 2J − 1`.
- `hsmall'` rewrites the coordinate finrank to `2J`.
- `hdV` and `selected_actual_source_dimension_bound` are both derived inline.
- The export adds no size premise. This confirms the author's rank-loss reconciliation note.

**Which factor-2 direction is used.** Both directions are used, each validly:
- **Mass bound (reverse direction).** `grassmannExperiment ≤ 2·matrixMoment` follows from `alpha_loss_bound`: `1 − α ≤ (c + m·s)·2^{c+s−1}/2^{2J} ≤ ½`, hence `α ≥ ½`. I re-checked it:
  - base loss: `c` terms;
  - extension loss: `1 − ρ^t ≤ t(1 − ρ)` with `t = m` and `w = s`;
  - `1 − ab^t ≤ (1 − a) + (1 − b^t)`.
- **Center beta (free direction).** `matrix ≤ Grassmann` follows from `α ≤ 1` at copy count 0.

**Selector output versus the instance index**
- `selector_unbounded` or `selector_eventually_exists`, specialised to the total floor `S j = max(analyticSourceHeightFloor …) (j+2)`, proves that some admissible `m` exists for all large `L`. This matches the author note.
- For a fixed `m`, admissibility is upward-closed in `L`: every conjunct is monotone because `hBlock L m`, `blockNum` and `RBlock` are nondecreasing in `L`. So `selector` is nondecreasing.
- What is not proved:
  - that every large `m` is ever hit, since with an arbitrary non-monotone `base` or `cutoff` the selector can skip values;
  - any effective `L₀`.
- **New finding.** One natural number `m` is simultaneously the row count of `Instance N m`, the selector output, the star arity (`k := m`) and the moment-window index. Joint inhabitance therefore needs a source instance with exactly the selected number of rows. This is a fidelity question, not a soundness defect.

**Claim that all untagged centers are vacuous (complexity-03, C1, rated HIGH)**
- Showing that no untagged center exists requires `J > (1 + 18·D)·m`, where `D = FixedPortCycleFamily.degree = algFamily.degree = widthBnd·fitD`.
- In that expression, `fitD = deg²` and `deg = 120^{fifthExp}`. `fifthExp` is `Classical.choose` of `∃ m, λ^m ≤ 1/5`, a witness with no provable upper bound.
- So the blanket conclusion is **unsupported**. It holds eventually in `m` for whatever constant `D` is, but it is not certifiable at any particular selected parameter.
- None of the questioned untagged declarations is reached. `ActualStarFixedRhoDimensionGuard` reaches only `leafT`/`leafK`.
- **Disposition:** downgraded to Info and treated as a non-claim. It does not block.

**Reached definitions versus source, star and expansion theorems.** The recorded closure confirms:
- From the star and source modules, the root reaches carrier definitions and dimension lemmas only: `matchingStarMass`, `MatchesStar`, `SideComplement`, `sideComplement_finrank`, the transported tables, `Instance`/`EqualityCloud`/`GraphEdges` types, `equationSpan_finrank_eq_card`, and `taggedCenterOver_nonempty`.
- It does not reach weighted selection, acceptance comparison, incidence reweighting, `cut_expansion`, or `kappa`.
- **Consequence:** the material bound concerns one fixed functional `f`. Linking verifier acceptance to such an `f` (the source/star route) is outside the export.

**Spectral47.** The reviewer orbit sketch below was re-derived but is **not machine-checked**.
1. Basis invariance gives `F̂(Z) = F̂(Z·U^{−T})`. Coefficients are therefore constant on the class of frequencies with a fixed column space W.
2. `appendAverage χ_Z` vanishes unless `Z = [Y | 0]`, and then equals `χ_Y`.
3. By Parseval, assuming the normalisation implied by `character_orthogonality`, the per-class energy ratio is `∏_{j<i}(2^c − 2^j)/(2^{c+s} − 2^j) ≤ 2^{−is} ≤ 2^{−i(s−1)}`.
4. The argument uses none of `hEven`, `ρ`, `hc`, `hs` or `hHeight`.

Two consequences:
- The contract looks provable for every cutoff, so `hSpectral` is very likely not a vacuity risk.
- The formal contract may be weaker than manuscript Spectral 4.7. That needs a fidelity check.

The contract stays **OPEN** until it is machine-proved and its manuscript fidelity is reviewed.

**Numeric NO**
- The RHS is `2^m·β^{1−m/k}·(Σ_{i≤r} 2^{500i²k}·(2e)^{(k−2)/k})^m + 2^m·a^m·β + B/a²`.
- Here `k ≥ 1024` and `B` is the sum of actual high-level energies. Any level `i ≥ 1` therefore needs `e` around `2^{−5·10⁵}`.
- The trivial choice `e = 1` satisfies `hfail` whenever agreement is at most 1, so the bound only has content with a small `e`.
- I verified the author's stationary-`a` algebra, `a* = (2B/(m·A₀))^{1/(m+2)}` giving value `(1 + m/2)·A₀·a*^m`. It is a candidate only, and does not hold at the boundary `B = 0` or `β = 0`.
- Usefulness is **OPEN**.

## Complexitylib boundary (23 bodies), reviewed separately from computability

**Mathematics.** No defect found. I checked by hand:
- RegularGraph and Mixing: contraction, two-sided squared `SpectralBound`, and the mixing lemma;
- EdgeExpansion and Union;
- Cheeger: co-area, Cauchy–Schwarz, median split, lazy walk `1 − h²/4`;
- the permutation-counting arithmetic: `3³¹ ≤ 2⁵²` and `2²⁰·3³¹⁰ ≤ 2⁵⁴⁰`;
- ExpanderExists: `λ = 1 − (1/600)²/4`;
- Power: `λ^t`;
- ZigZag: RVW bound `λ_G + λ_H + λ_H²` with polarisation;
- the tower invariant `4/25 + 1/5 + 1/25 = 2/5`;
- the merge at `m ≥ 3`: `0.633 ≤ 0.64`;
- FamilyFin: `famLam = √(1 − 27/(25W)) < 1`.

**Semantics of `algFamily`, padding and RegGraph**
- Graphs are multigraphs given by rotation involutions.
- Padding loops and empty merge slots become fixed darts, and `famRot 0 = id`.
- ActualGraphEdges excludes vertex-level loops (`IsRep` ⇒ `Nonloop`) and keeps parallel edges as distinct orbits. This is consistent with loops never crossing a cut.
- The degree is positive, and in fact `famDeg ≥ 3·deg² ≥ 12`.

**Reach**
- The 7 recorded boundary constants are `algFamily`, `ExpanderFamily.degree`, `degree_pos`, `graph`, `RegGraph`, `rot` and `relabel`.
- They enter only the type of `I`, as carrier data (degree and rotation) through Vertex/Edge/GlobalVar.
- The spectral and expansion facts are **not load-bearing** for the material conclusion.
- `#print axioms` is transitive across packages, so the standard root profile does cover `algFamily`'s classical closure. That is axiom evidence only; it is not review of every external body.

**Computability and runtime (non-claims)**
- `algBase := Classical.choose exists_finBase` is seeded from `randExpander`, and every definition is `noncomputable`.
- `ExpanderRandom` proves existence only.
- No runtime theorem exists, and the docstrings saying "explicit" or "an algorithm can read" are informal.
- The `Expander.lean` docstring saying the library has no Cheeger inequality or zig-zag product is stale.

## Reconciled findings

| ID | Origin | Declarations | Severity (prior → now) | Disposition / evidence | Remaining action |
|---|---|---|---|---|---|
| I1 | P7-F1, W2 H-1, R1-m | export / `selected_actual_material_moment_bound` | HIGH → **resolved** | Only `hHC` is removed; kernel `exact`; root profile standard | — |
| I2 | P7-F2 | `HC46ExactContract` vacuity | HIGH → **resolved** (prior) | `exactWholeRestriction` forces `η ≥ 0`; standard inhabitant | — |
| I3 | P2-3, C3, P5-6, C5-10 | `hsmall`, `hdV`, `grassmann_le_twice_moment` | Med → **resolved** | Derived inside AppendMoment; the reverse direction is valid | — |
| I4 | PA1-04, C-P2, NC F3 | `Spectral47ExactContract` | Med → **open (likely dischargeable)** | Orbit sketch above; hypotheses unused | Machine proof; fidelity to manuscript 4.7 |
| I5 | C4 (cx-03), author selector note | `hsel`, `selector` | Med → **partially resolved** | Existential output proved. A prescribed `m` is not proved, and skipping is possible with arbitrary floors | Prove hitting or monotonicity for the actual cutoff; give an effective `L₀` |
| I6 | new | `Instance N m` versus selector `m` and arity `k := m` | **Medium (fidelity)** | One `m` couples row count, arity and moment index | Manuscript check; joint-inhabitance witness |
| I7 | cx-03 C1 | untagged `QuestionCenter` guards | HIGH → **Info** | Blanket vacuity unsupported (classical `D`); declarations unreached | None for the material scope |
| I8 | P3-1, PA4-01, C5, N1, N2 | acceptance and selection theorems | Med → **confirmed unreached** | Reached-constant JSON | Source/star gate |
| I9 | PA4-02, P5-1, C2, N7 | Complexitylib, `hexpand`, `kappa` | Med → **resolved for the material scope** | Only carrier data reached; expansion not reached | Expansion and FP for the reduction gate |
| I10 | C1 (cx-04), C5-1, P5-6 | `blocks`, `algFamily` computability | Med → **retained (runtime)** | Doubly exponential `J`; noncomputable base | Encoded-reduction and runtime gates |
| I11 | PA1-05, P3, NC F4 | `selected_actual_analytic_rhs`, `hfail` | Med → **open** | `e = 1` is trivial; no usefulness theorem | Numeric NO |
| I12 | PA1-06 | `copies` | Info | Constrains only tagged nonemptiness and size | Joint inhabitance |
| I13 | PA1-03 | type identity | Low → **resolved** | `exact` is checked against the original type | — |
| I14 | PA1-02, banners | Application comment; MatrixGrassmannIdentity, PortCycleReplacement, SamplerParameters, CoveringSpan/TV, FixedPortCycleFamily banners; `Expander.lean` docstring | Low | Stale; no evidential weight either way | Clean up before render |
| I15 | P3-4, P2-5, N8 | in-module `#print axioms`; linter suppression | Low | Info output and suppression; zero owned warnings is not zero total warnings | Warning gate |
| I16 | C4 (cx-02), N5 | `E1_not_75/150/225` | Info (unconsumed) | Documented mismatch between formal and manuscript exponents | Fidelity gate |
| I17 | R4–R6 | PR one-sided `2e`, `r < d` | Retained | Boundary kept as stated | Wording |
| I18 | — | `Mathlib.Basic.Real.Basic` import path | Info | Resolves under the pinned Mathlib | Fresh-checkout replay |

**Missing bodies or profiles:** none for this scope. The original upstream seven-target profiles do not prove any CMMSA bridge, and their independent post-audit is pending.

## Safe conditional claim

Under the pinned kernel and Init/Mathlib/Batteries trust, the qualified native receipts (173 roots with standard profiles), the reviewed Complexitylib boundary, and identity-eligible reuse:

> For every `Instance N m` I, copies, `U : TaggedGoodU`, side complement A, globally fixed tagged tables C and T, and functional `f`, and for every `base`, `sourceHeightCutoff`, `L`, `samplerA ≥ 1` and `r < leafT + leafK`:
>
> if `selector(…) L = m`, `0 ≤ e`, `hfail(e)` holds on the same coordinate leaf table, `Spectral47ExactContract sourceHeightCutoff` holds, and `a > 0`,
>
> then there is a dyadic `k` with `4m ≤ k < 8m` such that
> - `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)`, and
> - the matching center mass equals the exact Grassmann center fraction.
>
> HC46 is discharged by `original_HC46_exact`. `hsmall` and the dimension guards are derived. The axiom profile is `{propext, Classical.choice, Quot.sound}`.

**Not claimed:**
- Spectral47;
- inhabitance of `hsel` at the instance `m` jointly with I, U and copies;
- a useful `e`, `a` or numeric NO bound;
- acceptance-to-functional, source, star or robust8S results;
- expansion, FP, encoded reduction, runtime or learning;
- upstream bridges;
- zero total warnings or a fresh checkout;
- novelty, citations, render or final providers;
- any manuscript acceptance.

## Remaining to-do

1. Machine-prove the Spectral47 orbit argument, or keep it as a premise, and audit fidelity to manuscript Spectral 4.7.
2. Settle the manuscript meaning of the `m` coupling (I6). Prove that the selector hits the fixed `m` for the actual cutoff, with an effective `L₀`, and exhibit a joint I/copies/U/A witness.
3. Prove `hfail` with a useful `e` on NO instances. Bound `B`, choose `a`, and compare `2·RHS` with the threshold.
4. Complete the source/star route from verifier acceptance to a fixed `f`, plus `AllAmbientInverse`/robust8S and the expansion discharge (`kappa`, `hexpand`).
5. Encoded reduction and runtime: doubly exponential `J`, an explicit expander table, and `rotVal` cost.
6. Upstream build and profile audit, plus the CMMSA bridges.
7. Warning and info-output disposition, removal of stale banners, and fresh-checkout replay.
8. Manuscript fidelity (constants, E1 exponents, PR wording), then render, novelty, citations and the final providers.
