# Full97 complexity review: two new bodies and the conditional material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **The two new bodies** (`BinaryMatrixSameRangeOrbit`, `SourceSizeContractBridge`), native and conditional | **GO-WITH-NOTES.** I found no soundness, direction, quantifier or vacuity defect. |
| **Conditional material integration** (184 roots, focused-16) | **GO-WITH-NOTES.** The material exports are byte-identical to Full95. The contract bridge, previously only definitional, is now explicit. No HIGH finding is open in this scope. |
| **Unconditional material readiness** | **NO.** Universal Spectral47 is not inhabited (`universal_Spectral47_inhabitant_proven: false`). There is no useful `e` and no numeric NO result. There is no joint witness for source, selector, `copies`, `U` and `A`. |
| **Overall full-goal GO** | **Not issued.** R14, a HIGH finding on the encoded reduction and runtime gate, is still open. The publication gates are also open. |
| **Manuscript, novelty, priority** | **No verdict.** I accept nothing in this scope. |

**Method.** I used no tools, wrote nothing, ran no Lean or Lake, used no subagents, and recomputed no hashes. Compile status, axiom profiles, trace and custody facts come from the supplied receipts. Hash comparisons below are string comparisons of the supplied hex. The author's notes and the reuse audit are evidence, not certificates.

## 1. Coverage

**Supplied complete bodies: 70. Inspected in this pass: 70. Skipped: 0.**

| Group | Files | Depth |
|---|---|---|
| New (2) | `BinaryMatrixSameRangeOrbit`, `SourceSizeContractBridge` | Every declaration, line by line |
| Sealed support (1) | `MatrixLiftAffineTarget` | Line by line: `surjective_target_orbit`, `splitSurjection`, and their dependencies. I read the remaining declarations for context only, since the new body uses none of them. |
| Full95 bodies (4) | SourceSize `AppendMoment`, `AnalyticMoment`, `OriginalApplication`; `ManuscriptDyadicMoment` | Re-checked the contract definitions, export signatures and integration call sites. I diffed both contract bodies against the legacy `AnalyticMoment`. |
| Critical prior bodies (5) | `HC46OriginalApplication`, `AnalyticMoment` (legacy), `AppendMoment` (legacy), `OriginalExactInhabitant`, `LeafLabelRankImageAlignment` | Re-checked contract definitions, the inhabitant's type and the export binders |
| Other reached project bodies (35) | `AppendFourierCrossLevelOrthogonality` … `TaggedFinite3LinSource`, as listed in the packet | Read in this pass. I re-derived only what the integration and the Spectral47 route consume, mainly `appendAverage_character`, the cross-level orthogonality and `actualLeafIndicator_mul_right_eq`. |
| Complexitylib (23) | `Cheeger` … `ZigZagTower` | Read. They are unchanged. Their mathematics was rechecked in earlier rounds, and I add no new credit. |

**Not supplied, and not re-read:**
- **278 project bodies**, out of 325 total minus 47 supplied. Examples are `BinaryMatrixFourier` (which holds Parseval and `fourier_inversion`), the `MatrixGrassmann*` modules, `ActualSourceStarLaw`, and the HC46 A6–A22/DR6/RealQ chain.
- **386 external files**, out of 409 minus 23.

These are credited only through identity reuse: 323 unchanged prior bodies, `changed_prior_bodies: []`, 8069 unchanged constant types and edges, and compiler, package and core configuration preserved. That is identity, not a re-reading.

**No required fresh body was skipped.**

## 2. New declarations

### `BinaryMatrixSameRangeOrbit.same_range_right_orbit`

```
{D C} [AddCommGroup D] [Module (ZMod 2) D] [FiniteDimensional (ZMod 2) D]
      [AddCommGroup C] [Module (ZMod 2) C] [Fintype C]
(f g : D →ₗ C) (h : range f = range g) : ∃ e : D ≃ₗ D, ∀ x, g (e x) = f x
```

| Check | Finding |
|---|---|
| Hypotheses | The only premises are equal ranges, a finite-dimensional domain and a finite codomain. There is no injectivity, rank or full-row-rank premise. |
| Codomain restriction | `W := range f`. `fr := f.rangeRestrict`. `gr := g.codRestrict W …`, whose membership proof rewrites by `h` into `range g` and is correct. |
| Surjectivity | `hfr` and `hgr` are each proved directly from range membership, through `Subtype.ext`. Neither is assumed. |
| Use of `surjective_target_orbit` | Genuine: it is instantiated at codomain `W` with `fr` and `gr`. I re-derived the lemma. `splitSurjection` gives `D ≃ C × ker`, whose first coordinate is the map itself. The kernel finranks agree because rank plus nullity holds and both ranges are ⊤. Then `e = sf ≫ (id × ke) ≫ sg⁻¹`, and so `g(e x) = (sf x).1 = f x`. |
| Direction | `g ∘ e = f`, so `e` is a **right** change of domain coordinates. This matches the docstring and the orientation that `basisInv` (`F (M*U) = F M`) consumes. |
| Subtype equality | `congrArg Subtype.val (he x)`, then `change`. This is a definitional unfolding of `rangeRestrict` and `codRestrict` and is sound. |
| Deficient and degenerate cases | Rank-deficient `f` and `g`: the kernel argument covers them. `f = g = 0`: `W = ⊥` is a singleton, both maps are surjective onto it, and the conclusion holds with `e` mapping into `ker g = D`. `D = 0`: trivial. No case is vacuous. |
| `[Fintype C]` | Harmless. It is inherited from the section variables of `MatrixLiftAffineTarget`, and `Fintype W` follows classically. It does not restrict the application at `C = Fin n → ZMod 2`. |
| Profile | {propext, Classical.choice, Quot.sound}, which is standard, as expected given `Classical.choose` in `splitSurjection`. |

**What it is not.** It is a statement about abstract finite-dimensional binary modules. It does not give:
- (a) the passage from `LinearEquiv` to a `BinaryMatrix` `U`/`V` pair with `U*V = 1`, `V*U = 1` and `toLin'` compatibility;
- (b) Fourier covariance, `F̂(Z) = F̂(Z·U^{-T})` under `basisInv`;
- (c) the converse (right orbit implies equal range) or any orbit or class cardinality;
- (d) the append-average energy and Parseval identities;
- (e) assembly into `Spectral47ExactContract`.

It is a root. It is not consumed by any material export, so `hSpectral` remains a premise everywhere.

### `SourceSizeContractBridge.hc46_contract_iff` and `spectral47_contract_iff`

Both are `Iff.rfl`, and the kernel accepted them. I compared the two retained bodies clause by clause:

| Clause | Legacy `ActualSelectedComplementAnalyticMoment` | SourceSize | Same? |
|---|---|---|---|
| HC46 binders | `{n d h r i p} {eta} (hEven : d = 2*h) (b : BinaryMatrix n d → Bool)` | identical, `_hEven` | ✓ (only the binder name differs) |
| HC46 carrier | Boolean `b`, via `indicator b` | same | ✓ |
| HC46 premises | `PseudorandomExact r eta b`, `i ≤ r`, `4 ≤ p`, `∃ q, p = 2^q` (dyadic) | same | ✓ |
| HC46 conclusion and budget | `lpNorm p (rankProjection i (indicator b)) ≤ 2^(500 i² p) · eta^((p−2)/p)`; `eta` unrestricted | same | ✓ |
| Spectral47 binders | `{n c s h i} {rho} (F : BinaryMatrix n (c+s) → ℝ)` (real-valued carrier) | same | ✓ |
| Invariance | `∀ M U V, U*V = 1 → V*U = 1 → F (M*U) = F M`, over **all** matrices (deficient included), with paired two-sided inverses | same | ✓ |
| Source guards | `c+s = 2h`, `i ≤ c+s`, `0 < rho`, `c = 2(1−rho)h`, `s = 2 rho h`, `cutoff rho ≤ h` | same | ✓ |
| Normalization | `uniformMean` on both sides, i.e. the unconditional `appendAverage` with a squared rank projection | same | ✓ |
| Spectral47 conclusion | `≤ (2^{−i(s−1)} + 3·2^{i−n}) · uniformMean (rankProjection i F)²` | same | ✓ |
| Cutoff quantification | `spectral47_contract_iff` is universal in `cutoff`, so transfer works at every caller cutoff | — | ✓ |

**Disposition.** Prior findings N-2, N3 and F3 (the implicit, definitional-only bridge between the duplicate contracts) are **resolved**. Consequences:
- `hc46_contract_iff.mp original_HC46_exact` now inhabits the SourceSize HC46 contract through a named lemma.
- `spectral47_contract_iff` only **transfers** a future inhabitant. It constructs none.
- Because the bridges are `Iff.rfl`, any later edit that makes the two bodies diverge will fail to compile. That is a useful guard, but the duplicate constants still exist.

## 3. A hand check of the Spectral47 orbit route (uncertified)

These steps re-derive the route by hand. None of them is machine-checked:

1. `basisInv` plus the character change of variables gives `F̂(Z) = F̂(Z·U^{-T})`. So `F̂` is constant on right orbits of frequencies `Z ∈ 𝔽₂^{n×(c+s)}`.
2. By `same_range_right_orbit` applied to `toLin' Z`, those orbits are exactly the column-space classes.
3. `appendAverage_character` (proved) keeps only `Z = [Y|0]`, and the rank of `[Y|0]` equals the rank of `Y`.
4. Parseval and orthogonality give:
   - LHS = `Σ_{rank Y = i} F̂([Y|0])²`;
   - RHS energy = `Σ_{rank Z = i} F̂(Z)²`.
5. For a column space `W` of dimension `i`, the ratio of class counts is `∏_{j<i}(2^c − 2^j)/(2^{c+s} − 2^j) ≤ 2^{−is} ≤ 2^{−i(s−1)}`.

**Consequences.**
- The formal contract appears provable for **every** cutoff, using none of `hEven`, `ρ`, `hc`, `hs`, `hHeight`, or the `3·2^{i−n}` slack.
- So `hSpectral` is very unlikely to be a vacuity risk.
- It also suggests the formal contract is weaker than manuscript 4.7, which remains an open fidelity question.
- What is still missing is (a)–(e) from §2, plus Parseval from the unsupplied `BinaryMatrixFourier`.

## 4. Integration (re-confirmed from the bodies)

- **Same objects throughout.** The SourceSize and Dyadic exports use the same `I`/`copies`/`U`/`A`/`C`/`T`/`f`. The same `Tc = selectedCoordinateLeafTable` appears in `hfail`, in the PR premise and in the moment. The same `Cc`/`fc` appear in the center identity. There is no selected-leaf surrogate, no uniform or rank-one replacement of the append experiment, and no narrowing of the source or star family.
- **Source row count.** It is independent of the leaf query count: `Instance N rows`, where `m` is only the selector output, star arity, moment base and `bOf` parameter.
- **SourceSize dimensions.** `c+s = 2h ≤ 2J = finrank A.1`. The quantities `hdim`, `hD` and `hsmall` are derived (rank loss ≤ ½). The guards `hrd : r < c+s` and `1 ≤ samplerA` are retained.
- **HC46.** The original inhabitant `original_HC46_exact` is applied through the universal contract with `hEven := hsplit`.
- **Dyadic exponent.** It is chosen by the caller: `4m ≤ k`, dyadic, with no upper bound. The derived guards are `4 ≤ k` and `m ≤ k`.
- **Floor and cutoff.** `analyticSourceHeightFloor base cutoff` is the same cutoff that is passed to `hSpectral` at `ρ = 1/bOf m`.
- **No guard was weakened.** Object hashes of the four Full95 modules are **identical** in the Full95 mapping and in the Full97 typed record (for example, Dyadic `C02909B6…9E1F`). That is consistent with `cache_objects_unchanged` and with no semantic change to the material exports.
- **Selection versus mathematical obligations.** "Generic body selection is complete" is distinct from the mathematical obligations around source, pre-draw selection and the global table. The latter remain open (`source_selection_complete: false`).

## 5. Typed hash custody

| Path | `source_sha256` (header = typed record) | `compiled_object_sha256` (typed = legacy `added_object_hashes` value) |
|---|---|---|
| ManuscriptDyadicMoment | AF3E380A…A705 ✓ | C02909B6…9E1F ✓ |
| SourceSizeAnalyticMoment | 03FB0A5D…D3D1 ✓ | B472BC2E…6EB6 ✓ |
| SourceSizeAppendMoment | D4B86B56…5817 ✓ | 6E8EA03C…341D ✓ |
| SourceSizeOriginalApplication | 22DE415F…6C08 ✓ | 3268034A…E7D9 ✓ |
| BinaryMatrixSameRangeOrbit | 8864F115…3EE7 ✓ | 35D10224…69D4 ✓ |
| SourceSizeContractBridge | 022E14E6…E255 ✓ | F64A52BA…66FB ✓ |

- **Category separation.** I keep the two categories apart. The legacy field still holds **object** digests under `.lean` keys, and I do not read it as source hashes.
- **H-1/H1 stay closed,** as all three Full95 addenda found. I am not reopening them.
- **Sizes.** `MatrixLiftAffineTarget` header `4169A269…C5EF` is not cross-checkable against an old index here, because the index members were not supplied.

## 6. Findings

| ID | Sev. | Declarations | Evidence | Disposition and action |
|---|---|---|---|---|
| CX97-01 | Verified | `same_range_right_orbit` | §2: hypotheses, surjectivity, direction, subtype equality and degenerate cases all check, and the lemma is used genuinely | Credit as a generic binary-module orbit lemma |
| CX97-02 | **Medium, open** | Spectral47 bridges (a)–(e) | The helper is unconsumed. `universal_Spectral47_inhabitant_proven: false`. §3 is a hand sketch. | Prove the matrix-action, Fourier-covariance, cardinality, append-energy and assembly bridges; audit fidelity to 4.7 |
| CX97-03 | Low | `same_range_right_orbit` | `[Fintype C]` is inherited and not needed by the proof | Optional generalization; no effect on soundness |
| CX97-04 | Resolved (was Low N-2/N3/F3) | `hc46_contract_iff`, `spectral47_contract_iff` | Clause-by-clause identity (§2); kernel `Iff.rfl` | Transfer is explicit; the HC46 inhabitant transfers. Still to do: choose one canonical contract constant. |
| CX97-05 | Info (non-claim) | `spectral47_contract_iff` | `Iff` transfers inhabitants only | Never cite it as Spectral47 evidence |
| CX97-06 | Low (hygiene) | Native report `added_object_hashes` | Still keyed by source path but holding object values; typed records now coexist | Retire the legacy field, or rename it `object_hash_by_source_path` |
| CX97-07 | Low (evidence tier) | Full97 typed identities | They live only inside the qualified report (`DFB65C0D…`). No member listings of the before/after seals were supplied. | ID-2 remains: recompute from custody `693105…` and the trace `6EC526…` during fresh-checkout replay |
| CX97-08 | Info | Bookkeeping | 172+12 = 184 roots; 13+3 = 16 focused; 8069+3 = 8072 nodes; 323+2 = 325 bodies; 2738 external boundaries unchanged. That last point fits the new roots using only already-reached external constants (an inference). | Consistent |
| CX97-09 | Low (stale) | `SourceSizeOriginalApplication` comment ("not compiled"), Dyadic header ("Uncompiled candidate"), orphan Dyadic `/-! Scalar … -/`, legacy `AnalyticMoment` "not claims proved locally" | Contradicted by the receipts; no weight either way | Clean up before render |
| S1, S2, S3 | Medium, open (carried) | Spectral47; `selected_actual_analytic_rhs`/`hfail`; the `copies`/`U`/`A` joint witness | Unchanged | See the to-do list |
| R14 | **HIGH, open** (reduction/runtime gate only) | `blocks`, `hBlock`, `algFamily` | `J ≈ 2^{2^{A h²}}`. There is no implicit encoded reduction and no runtime theorem. Parameter size alone neither proves nor disproves anything. | **Bars overall GO** |

## 7. Reconciliation with earlier reports

- **All three original Full95 lenses and all three addenda** are preserved. Their conditional GO-WITH-NOTES verdicts stand. H-1/H1 stays closed as a category mismatch. ID-1/H-1a is partly mitigated by the typed records (CX97-06). ID-2 is open (CX97-07).
- **The 18 inherited Full90 reports** are preserved:
  - The N-1/I3/R5 row coupling remains resolved for the SourceSize roots, and the old roots are still `m`-coupled.
  - These remain non-claims: untagged-center vacuity, Rel-acceptance positivity, unreached selection and incidence, and Complexitylib runtime (X1–X5).
  - Numeric NO is still open. Untagged vacuity is still an unsupported non-claim.
- **New.** Prior N-2/N3/F3 are resolved (CX97-04). Spectral47 is narrowed: the orbit-equivalence ingredient now exists, but the bridges are open (CX97-02).

## 8. Safe conditional claim

Under the pinned kernel and Init/Mathlib/Batteries trust, the Full97 qualified receipts (184 standard profiles, seven exits of 0, 325 sources, 8072/8072 exact type edges) and identity reuse of the 323 unchanged bodies:

1. **The same-range lemma.** For finite-dimensional binary modules `D` and finite `C`, any two linear maps `D → C` with equal range satisfy `g ∘ e = f` for some automorphism `e` of `D`.
2. **The contracts.** The legacy and SourceSize HC46 and Spectral47 contracts are definitionally equivalent, the latter for every cutoff.
3. **The material bound.** The Full95 material bound is unchanged. For any `I : Instance N rows` (with `rows` independent of `m`) and any `copies`, `U`, `A`, `C`, `T`, `f`, `base` and `cutoff`, suppose `hsel`, `1 ≤ samplerA`, `r < c+s`, `0 ≤ e`, `hfail(e)` on the same `Tc`, `Spectral47ExactContract cutoff` and `a > 0` all hold. Then, with HC46 discharged by `original_HC46_exact`:
   - `matchingStarMass ≤ 2·selected_actual_analytic_rhs(Cc, Tc, fc, r, k, 2e, a)` at some dyadic `k ∈ [4m, 8m)`, or at any caller-chosen dyadic `k ≥ 4m` for the Dyadic export;
   - the center mass equals the exact Grassmann fraction.

**Not claimed:**
- universal Spectral47, any matrix, Fourier, cardinality or append-energy bridge, or fidelity to 4.7;
- numeric NO or a useful `e`/`a`;
- joint witnesses for source, selector, `copies`, `U` and `A`, or an effective `L₀`;
- source/star/robust8S, the pre-draw global table, or the physical sampler;
- encoded runtime, reduction or learning (R14);
- upstream or CMMSA bridges;
- zero total warnings (inherited warning debt is explicit even though owned and regression gates are zero), or a fresh checkout;
- novelty, citations, PDF or publication;
- any unconditional theorem or manuscript acceptance.

## Remaining to-do

1. **Spectral47 bridges:**
   - correspondence between `LinearEquiv` and paired-inverse `BinaryMatrix` under `toLin'`;
   - Fourier covariance `F̂(Z) = F̂(Z U^{-T})` from `basisInv`;
   - the converse of the orbit lemma, plus counts of column-space classes and surjections;
   - append-average energy via Parseval (`BinaryMatrixFourier`);
   - assembly of an inhabitant of `Spectral47ExactContract`, transferred through `spectral47_contract_iff`;
   - the fidelity audit against manuscript 4.7, given that the source guards are unused.
2. **Canonical contract.** Pick one canonical contract constant, and mark the old `m`-coupled roots as superseded.
3. **Numeric NO.** Certify the scalar consumer (`r`, `T`, dyadic `P`, `B ≤ 2^{−r(s−1)}`, Parseval `ΣEᵢ ≤ 1`, `base`/`cutoff` including `h > 20000m³`, effective `L₀`). Then prove `hfail` at a useful `e` and compare against the actual selection threshold.
4. **Joint witness** for `I` (rows ≥ 1), padded `copies`, `TaggedGoodU` at `J`, `A` and `hsel`.
5. **Source/star/robust8S** and the pre-draw global table (`AllAmbientInverse`, `kappa`/`hexpand`, MZ completeness 1−η). Close `source_selection_complete`. Add the physical sampler.
6. **R14:** an encoded or implicit reduction and runtime proof for the doubly exponential `J`, with explicit expander tables and `rotVal` cost. Learning.
7. **Upstream:** the seven-target post-audit, then the exact CMMSA bridges.
8. **Hygiene:**
   - retire the legacy source-keyed object field (CX97-06);
   - recompute all six source and object hashes from custody during a fresh-checkout replay (CX97-07);
   - remove stale banners (CX97-09);
   - dispose of the inherited warnings, linter suppression and in-library `#print axioms` output.
9. **Release:** manuscript fidelity (E1 exponents, constants, PR wording, rows/m semantics), exhaustive novelty and citation review, BibTeX and PDF QA, and the final full-scope providers.
