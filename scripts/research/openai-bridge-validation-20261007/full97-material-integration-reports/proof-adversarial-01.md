# Proof-adversarial review: Full97 two new bodies and the whole conditional material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **Two new bodies:** `BinaryMatrixSameRangeOrbit`, `SourceSizeContractBridge` | **Verified.** I found no soundness, direction, quantifier or vacuity defect. |
| **Native and conditional material integration:** 184 requested roots, the exact 184 and focused 16 trace graphs, SourceSize and Dyadic exports | **GO-WITH-NOTES, conditional.** No HIGH is open in this scope. The Full95 conditional verdict carries forward unchanged, because the bytes of the four Full95 bodies are identical. |
| **Overall GO** | **Not issued.** R14, a HIGH on the encoded reduction and runtime gate, is still open. The other full-scope gates are also open. |
| **Unconditional material readiness** | **No.** Spectral47 is still a premise. There is no inhabitant, no numeric NO bound, and no joint witness. |
| **Manuscript, novelty, priority** | **No verdict.** Nothing is accepted. |

**How I reviewed.** I used no tools, made no writes, and ran no Lean, Lake or subagents. I recomputed no hashes; every hash comparison below is a string comparison of values in the packet. Native, compile, profile and trace facts come from receipts. Receipts are evidence of what happened, not acceptance.

## 1. Coverage

| Body set | Count | Status |
|---|---|---|
| `BinaryMatrixSameRangeOrbit.lean` (new) | 1 | **Read in full.** Every declaration checked. |
| `SourceSizeContractBridge.lean` (new) | 1 | **Read in full.** Both bridges checked against both full contract definitions. |
| `MatrixLiftAffineTarget.lean` (sealed support, unchanged) | 1 | **Read in full.** I re-derived `splitSurjection` and `surjective_target_orbit` line by line. The other declarations were read, but not re-derived, because the new root does not reach them. |
| Full95 new bodies: SourceSize AppendMoment, AnalyticMoment, OriginalApplication; Dyadic | 4 | **Re-read** at the consumption interfaces: contract definitions, `rows` binder, `hHC rfl`, the dyadic guards, the export statements. |
| Other supplied prior project bodies | 40 | **Supplied and inspected at the interfaces** the new roots and exports use. The full line-by-line review of these is the prior per-lens review, reused by identity. |
| Complexitylib | 23 | **Supplied.** No new consumer. The prior Complexitylib review is reused. |
| Unchanged project bodies not supplied | 278 | **Not read.** Identity reuse only: 8069 unchanged shared constant types and edges, configuration preserved. |

**Skipped required fresh bodies: none.** The only new or changed bodies are the two listed first, and both were read completely. The audit's `changed_prior_bodies` list is empty.

Totals: 325 = 323 unchanged + 2 new. Of the 323 unchanged, 45 are supplied (44 prior + MatrixLiftAffineTarget) and 278 are not.

## 2. `BinaryMatrixSameRangeOrbit.same_range_right_orbit`

**Statement.** For a finite-dimensional ZMod 2 space `D` and a finite ZMod 2 module `C`: if `f g : D →ₗ C` satisfy `range f = range g`, then there is `e : D ≃ₗ D` with `g (e x) = f x` for every `x`.

**Proof as checked:**
- `W := range f`.
- `fr := f.rangeRestrict`. Its surjectivity is shown directly from `mem_range`.
- `gr := g.codRestrict W`. Membership follows from `h`: `g x ∈ range g = range f`. Surjectivity follows by rewriting `range f` back to `range g`.
- `MatrixLiftAffineTarget.surjective_target_orbit fr gr` gives `e` with `gr (e x) = fr x`. Projecting with `Subtype.val` gives `g (e x) = f x`. The orbit lemma is genuinely used; it is not bypassed.

**`surjective_target_orbit`, re-derived:**
- `splitSurjection f` is built as `f.prod (id − s∘f)|ker` with inverse `(c, x) ↦ s c + x`, where `f∘s = id`. Both inverse laws check: `f(s c + x) = c`, `(s c + x) − s(f(s c + x)) = x`, and `s(f x) + (x − s(f x)) = x`.
- Rank–nullity, with `range = ⊤` on both sides, gives `finrank ker f = finrank ker g`. That yields `ofFinrankEq`.
- `e = sf ⋯ (id × ke) ⋯ sg⁻¹` gives `(sg (e x)).1 = (sf x).1 = f x`.

**The points you asked about:**
- **Hypotheses.** `FiniteDimensional D` is needed only for rank–nullity. `[Fintype C]` lets `W` inherit a classical Fintype instance. Neither hypothesis is vacuous.
- **Restriction to the range.** The codomain is narrowed to the actual common image `W`, never to a hypothesised surjection onto `C`. Surjectivity onto `W` is proved, not assumed.
- **Direction.** The conclusion is `g ∘ e = f`, a right action on the domain. Since `e` is an existential equivalence, the reverse orientation follows from `e.symm`.
- **Subtype equality.** The conclusion is obtained by `congrArg Subtype.val`, which is sound.
- **Deficient maps.** No injectivity or rank premise appears, so the result covers rank-deficient `f` and `g`.
- **Zero-dimensional cases.** `D = 0`, `W = ⊥`, or `C` trivial all go through the same proof: the split equivalences are trivial and the kernels both equal `D`.

**What it does not prove.** This is a statement about linear maps on finite-dimensional ZMod 2 modules. It is **not** stated for `BinaryMatrix`. The following steps are still missing:
- translating `e` into a matrix pair `U, V` with `U*V = 1`, `V*U = 1`, and `Y' * U = Y`;
- Fourier covariance. The step I expect is `pairing(Y'U, M) = pairing(Y', M Uᵀ)`, so that `basisInv` makes `F̂` constant on column-space classes of frequencies. That is my sketch, not a proved lemma;
- orbit cardinalities, including the `[Y | 0]` counting through `appendAverage_character`;
- Parseval and the per-class ratio `∏(2^c − 2^j)/(2^{c+s} − 2^j) ≤ 2^{−i(s−1)}`;
- absorbing the `3·2^{i−n}` slack;
- any universal inhabitant of `Spectral47ExactContract`.

The report agrees: `universal_Spectral47_inhabitant_proven: false`.

**Not on the export path.** This root is standalone. Every export still takes `hSpectral` as a premise.

## 3. `SourceSizeContractBridge`

**`hc46_contract_iff : legacy ↔ SourceSize := Iff.rfl`.** I compared the two definitions component by component and they match:
- the binders `{n d h r i p} {eta}`;
- the evenness guard `d = 2h`, named `hEven` in one and `_hEven` in the other;
- the Boolean carrier `b : BinaryMatrix n d → Bool`;
- the budget `PseudorandomExact r eta b`;
- the guard `i ≤ r`;
- `4 ≤ p` and the dyadic condition `∃ q, p = 2^q`;
- the normalized `lpNorm p (rankProjection i (indicator b))`;
- the bound `2^{500 i² p} · eta^{(p−2)/p}`.

The only difference is binder names. No basis-invariance premise and no `eta ≤ 1` premise is added in either.

**`spectral47_contract_iff cutoff := Iff.rfl`.** Again the components match:
- the function carrier `F : BinaryMatrix n (c+s) → Real`;
- all-matrix invariance under paired two-sided inverses, `basisInv` versus `_basisInv`, quantified over all `M` including deficient ones;
- the guards `c+s = 2h`, `i ≤ c+s`, `0 < rho`, `c = 2(1−rho)h`, `s = 2rho·h`, and `cutoff rho ≤ h`;
- the identical squared-energy conclusion, including the `3·2^{i−n}` term and the normalization by `uniformMean`.

Both files open the same namespaces for `appendAverage`, `rankProjection` and `uniformMean`. Kernel acceptance of `Iff.rfl` certifies definitional equality.

**Dispositions:**
- Full95 N-2 / N3 / F3 (the duplicated contracts) moves from **Low to closed**.
- **Caveat:** each `Iff` transfers an inhabitant if one exists. It constructs none. It also inherits the open fidelity question: `rho`, `hHeight`, `hc`, `hs` and `hEven` look unused by the orbit argument.
- **Info:** the exports were not refactored onto a single contract. The `Iff.rfl` now acts as a compile-time guard: if the two definitions ever diverge, the build fails.

## 4. Integration re-confirmation (unchanged bytes)

The source SHAs of the four Full95 bodies match their headers. So the Full95 checks hold unchanged:
- **Same objects throughout.** The same I, copies, U, A, C, T and f are used. `Tc` appears in `hfail`, the PR premise and the moment.
- **Row count.** `rows` is independent of the leaf count `m`.
- **SourceSize dimensions.** `c+s = 2h ≤ 2J`, and `hdim`, `hD` and `hsmall` are derived.
- **HC46.** The original `original_HC46_exact` is applied through the universal contract with `hEven := hsplit`.
- **Dyadic exponent.** The caller chooses it, subject to `4m ≤ k`. `hklt` was never used, so dropping it is sound.
- **Guards kept.** `hsel`, `hA`, `hrd`, `he`, `hfail`, `hSpectral` and `ha` are all still present.
- **Experiment not replaced.** The actual append experiment stands; it is not swapped for uniform or rank-one noise, and the source and star family is not narrowed.
- **Selected profiles.** The upstream selected native profiles are still not treated as CMMSA bridges.

## 5. Typed custody

**`added_source_object_identities`, six entries:**
- Each source SHA equals the supplied header. For the new files: `8864F115…3EE7` for SameRangeOrbit and `022E14E6…E255` for the Bridge. The four Full95 entries match their headers too.
- Each object SHA equals the value under the same key in the legacy `added_object_hashes`. For the new files: `35D10224…69D4` and `F64A52BA…66FB`.
- The four Full95 pairs, in both categories, are identical to the Full95 mapping `CB97732C…`.

**No category mixing.** No source hash and object hash coincide. The legacy field still uses source-path keys with object-hash values. It is labelled as retained for compatibility and I did not read it as source hashes. The Full95 H-1 closure stands.

**Info:**
- `MatrixLiftAffineTarget` `4169A269…` appears only as a header. I could check it only against the reuse index's inclusion, not against a per-file hash.
- Bookkeeping is consistent: 172 + 12 = 184; 181 + 3 = 184; focused 13 + 3 = 16.
- Trace nodes 8072 = 8069 + 3 is consistent with three new roots whose closures were otherwise already in the graph (for example, MatrixLiftAffineTarget). That is plausible, but no per-node enumeration was supplied.
- External boundaries are 2738, unchanged.
- These flags remain open or historical, as in the prior addenda: `consumption_trace_complete`, `material_body_review_complete`, `source_selection_complete` and `independent_body_review_complete`, all false.

## 6. Findings

| ID | Sev. | Declaration | Disposition | Action |
|---|---|---|---|---|
| SR-1 | Verified | `same_range_right_orbit` | Sound, generic, uses `surjective_target_orbit` | none |
| SR-2 | Info | the same | Name says BinaryMatrix; the statement is about linear maps | Add the matrix-pair (`U*V=1`, `V*U=1`) translation |
| SR-3 | Medium, open (carries N-6) | `Spectral47ExactContract` | The orbit lemma is one ingredient of five | Covariance, counting, Parseval, slack, inhabitant |
| SR-4 | Info | root placement | Not on any export path | none |
| CB-1 | Verified; closes N-2 | `hc46_contract_iff`, `spectral47_contract_iff` | Full component match | none |
| CB-2 | Low | both contracts | Fidelity to manuscript 4.7 unaudited; hypotheses unused | Fidelity audit |
| ID-1 | Verified | typed identities | All six pairs consistent | Ship the members of the before/after seals |
| N-4 | Low (carried) | Banners in Dyadic ("Uncompiled candidate") and SourceSize/legacy OriginalApplication ("not compiled") | Stale; the two new files are clean | Clean up |
| R14 | **HIGH (outside scope)** | encoded reduction | Open; parameter size neither proves nor refutes it | Proof |

## 7. Safe conditional claim

This rests on pinned kernel and Init/Mathlib/Batteries trust, the 184 standard profiles, the qualified trace, the typed identities, and identity reuse.

The Full95 SourceSize and Dyadic material bounds hold as stated: for every `rows`, I, copies, U, A, C, T, f, base and cutoff; under `hsel`, `hA`, `r < c+s`, `0 ≤ e`, `hfail(e)`, `Spectral47ExactContract cutoff` and `a > 0`; with HC46 discharged.

In addition:
- same-range linear maps on a finite-dimensional ZMod 2 space differ by a domain automorphism;
- the legacy and SourceSize HC46 and Spectral47 contracts are definitionally equivalent.

**Not claimed:**
- the matrix, Fourier, cardinality or append-energy bridges;
- universal Spectral47 or its fidelity;
- numeric NO or a useful `e` with `hfail`;
- joint source/selector/copies/U/A witnesses;
- source/star/robust8S or the pre-draw global table;
- the physical sampler;
- encoded runtime, reduction or learning;
- CMMSA bridges;
- zero total warnings, or a fresh checkout;
- novelty, citations, PDF or publication;
- overall GO.

## Remaining to-do

1. **Spectral47 in Lean.** Translate `e` into a matrix pair; prove frequency-class covariance of `F̂` under `basisInv`; prove the orbit counts (`[Y|0]`) and the per-class ratio; Parseval; absorb `3·2^{i−n}`; produce a universal inhabitant; transfer it through `spectral47_contract_iff`; then the 4.7 fidelity audit.
2. **Numeric NO.** A certified scalar consumer: choose r, T and dyadic P; prove ΣE ≤ 1; prove `hfail` with a useful `e`; instantiate `base` and `cutoff`; give an effective L₀; compare against the actual selection bound.
3. **Joint witness** for I, copies, U, A, C, T, f and `hsel`.
4. **Source/star.** Acceptance → fixed `f`; robust8S / `AllAmbientInverse`; the pre-draw global table; the physical sampler; `kappa` and `hexpand`; set `source_selection_complete`.
5. **R14.** Encoded reduction and runtime, implicit handling of `J`, explicit expander, learning.
6. **Upstream.** Post-audit, then the exact CMMSA bridges.
7. **Custody.** Supply the members of the before/after seals and the per-node trace enumeration.
8. **Hygiene.** Stale banners; mark the old m-coupled roots as superseded; dispose of the inherited warning debt and linter suppression; replay from a fresh checkout.
9. **Release.** Manuscript fidelity (E1, constants, PR wording, rows/m); novelty and citation checks; BibTeX and PDF QA; the final providers.
