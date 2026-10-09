# Full97 non-claims review: the two new bodies and the conditional material integration

## Verdicts

| Scope | Verdict |
|---|---|
| **The two new bodies** (`BinaryMatrixSameRangeOrbit`, `SourceSizeContractBridge`) | **GO-WITH-NOTES.** No soundness, direction, quantifier or vacuity defect. |
| **Native and conditional material integration** (184 roots, the material exports unchanged) | **GO-WITH-NOTES, conditional.** No HIGH in this scope. The three new roots run parallel to the material lane and do not feed into it. |
| **Unconditional material readiness** | **NO.** Universal Spectral47 is still a premise (`universal_Spectral47_inhabitant_proven: false`). Numeric NO, a useful `e`, and joint witnesses are still open. |
| **Overall GO** | **Not issued.** R14 is still an open HIGH on the encoded reduction and runtime gate, outside the material scope. |
| **Manuscript, novelty, priority, publication** | **No acceptance.** |

**Method.** I used no tools, writes, Lean/Lake runs or subagents, and recomputed no hashes. Compile status, axiom profiles, trace and custody facts come from the supplied receipts. Hash comparisons below are string comparisons of supplied values.

## 1. Coverage

**Supplied complete bodies: 70. Inspected: 70. Skipped: 0.**

- **2 new bodies, read line by line:**
  - `BinaryMatrixSameRangeOrbit.lean` (source 8864F115…3EE7)
  - `SourceSizeContractBridge.lean` (source 022E14E6…E255)
- **Sealed support, read in full:** `MatrixLiftAffineTarget.lean`. I re-checked `splitSurjection`, `surjective_target_orbit` and the column-change lemmas, because the new orbit theorem consumes `surjective_target_orbit`.
- **The prior 67 bodies (44 project + 23 Complexitylib):**
  - They were re-supplied unchanged. The reuse audit lists them as unchanged, and `changed_prior_bodies` is empty.
  - I re-checked only the interfaces that the new bodies touch: the legacy and SourceSize `HC46ExactContract` and `Spectral47ExactContract` definitions, and the material and dyadic export binders.
  - I do not claim a fresh line-by-line proof re-read beyond that. The Full95 per-lens reviews remain the provenance for those bodies.

**Not supplied, so not reread:**
- 278 project bodies (325 − 47 supplied project bodies) are covered by identity reuse only: 8069 constant types and edges unchanged, compiler, package and core configuration preserved.
- 386 of the 409 external files are covered by pinned trust only.

## 2. New declarations

| Declaration | Severity | Finding |
|---|---|---|
| `BinaryMatrixSameRangeOrbit.same_range_right_orbit` | Verified (with Info notes) | Details in §3 |
| `SourceSizeContractBridge.hc46_contract_iff` | Verified | `Iff.rfl`; exact equality of the two Props (§4) |
| `SourceSizeContractBridge.spectral47_contract_iff` | Verified | `Iff.rfl` for every `cutoff`; it transfers an inhabitant and does not construct one (§4) |

The proof-internal `let`s and `have`s in the orbit theorem (`W`, `fr`, `gr`, `hfr`, `hgr`) are not exported.

## 3. Audit of `same_range_right_orbit`

**Hypotheses.**
- `D` is any `FiniteDimensional (ZMod 2)` module.
- `C` is any `Fintype` `ZMod 2`-module. `Fintype` is needed only to meet the signature of `surjective_target_orbit`. It is harmless for the intended case `C = Fin n → ZMod 2`.
- `f, g : D →ₗ C` with `range f = range g`.
- No rank, injectivity or surjectivity hypothesis on `f` or `g`.

**Range and codomain restriction.**
- `W := range f`.
- `fr := f.rangeRestrict` is surjective onto `W` by construction.
- `gr := g.codRestrict W …` is well defined because `g x ∈ range g = range f`.
- `gr` is surjective because every `w ∈ W = range g` has a `g`-preimage. The use of `h` points in the right direction.

**The orbit step.**
- `surjective_target_orbit fr gr` gives `e : D ≃ₗ D` with `gr (e x) = fr x`. I re-checked that lemma:
  - `splitSurjection` gives a genuine linear equivalence `D ≃ C × ker` in both directions.
  - Kernel ranks are equal by rank–nullity with `range = ⊤`.
  - `e = sf ≫ (id × ke) ≫ sg⁻¹`, hence `g ∘ e = f` on first components.
- `congrArg Subtype.val` followed by `change` reduces this to `g (e x) = f x`, using `codRestrict_apply` and `rangeRestrict_apply` definitionally. Subtype equality is handled correctly.

**Direction.** Precomposing `g` with `e` recovers `f`. In matrix terms, this is the shape needed for `Z' = Z·U` with the same column space.

**Edge cases.**
- Deficient maps are covered, including `f = g = 0`, where `W = ⊥` and every `e` works.
- `dim D = 0` gives `e = refl`.
- This generality is genuinely needed, because Spectral47's `basisInv` quantifies over all matrices.

**What it does not prove:**
- The statement is about abstract finite-dimensional modules. Despite the file name, it is not about `BinaryMatrix`.
- No matrix form exists yet: same `range (toLin' Y)` ⇒ ∃ `U, V` with `U·V = V·U = 1` and `Y' = Y·U` (via `toMatrix' e` / `toMatrix' e.symm`).
- None of the remaining Spectral47 steps is proved: the character transport χ_Y(MU) = χ_{YUᵀ}(M), constancy of the Fourier coefficients of a `basisInv` function on column-space classes, the restriction of the append operator to `[Y|0]`, the orbit and cardinality ratio ∏(2^c−2^j)/(2^{c+s}−2^j), the Parseval/energy bridge, and universal Spectral47.
- No material root consumes this theorem. `hSpectral` is still an explicit premise of every export.

## 4. Audit of the two contract equivalences

I compared the retained legacy definitions (`ActualSelectedComplementAnalyticMoment`) with the SourceSize definitions token by token.

**HC46:**
- The binders `{n d h r i p} {eta}` match.
- `(hEven | _hEven) : d = 2*h` differ only in name.
- The Boolean carrier `b : BinaryMatrix n d → Bool` is the same.
- `PseudorandomExact r eta b`, `i ≤ r`, `4 ≤ p` and the dyadic `∃ q, p = 2^q` match.
- The conclusion `lpNorm p (rankProjection i (indicator b)) ≤ 2^(500·i²·p) · eta^((p−2)/p)` matches.
- No `basisInv` or `eta ≤ 1` premise is added on either side.

**Spectral47:**
- The real carrier `F : BinaryMatrix n (c+s) → Real` is the same.
- `basisInv` is the same on both sides: it quantifies over all `M`, with paired two-sided inverses `U·V = 1`, `V·U = 1`, and deficient inputs included.
- `hEven`, `hi : i ≤ c+s`, `hRho`, `hc`, `hs` and `hHeight : cutoff rho ≤ h` match. Only the underscores differ.
- The normalization matches: `uniformMean` of `(appendAverage (rankProjection i F) M)^2` on the left, and `(2^(−i(s−1)) + 3·2^(i−n)) · uniformMean (rankProjection i F)^2` on the right.

**Elaboration context.** Both files use the same `open` set and the same `attribute [local instance] Classical.propDecidable`. So both elaborate the same constants, and `Iff.rfl` being kernel-accepted confirms definitional equality. The Spectral47 bridge holds pointwise in `cutoff`, so it transfers at the export's own `sourceHeightCutoff`.

**Disposition.** This closes, as Info, the earlier Low findings that the duplicate contracts had only an implicit bridge (Full95 N-2, N3 and F3). A future proof of either contract can now serve both the legacy and SourceSize roots through `.mp`/`.mpr`. Kernel definitional equivalence transfers an inhabitant; it does not construct one.

## 5. Typed custody (no category error reopened)

- The new `added_source_object_identities` entries for both new files match the body headers on the source side:
  - 8864F115…3EE7 and 022E14E6…E255.
- They also match the legacy dictionary on the object side:
  - 35D10224…69D4 and F64A52BA…66FB.
- The four Full95 typed pairs are unchanged from the preserved Full95 mapping.
- The legacy `added_object_hashes` field still keys object digests by source path. It is now explicitly labelled `legacy_source_keyed_object_hash_field_retained_for_compatibility`, and I read it only as object hashes.
- This resolves the earlier labelling item (H-1a / ID-1 / I-1) for the current report. The membership of these hashes inside the native seals remains receipt-tier, as before (ID-2).
- **Bookkeeping checks:**
  - 172 + 12 = 184 roots.
  - 323 + 2 = 325 sources.
  - The trace has 8072 = 8069 + 3 nodes, and the focused set has 16 = 13 + 3 entries.
  - The trace lists all three new or support modules.
- `consumption_trace_complete: false` and `source_selection_complete: false` are still current.

## 6. Whole conditional material integration (unchanged from Full95)

All of the Full95 material checks still hold, because the bodies are identical:
- The same `I`, copies, `U`, `A`, `C`, `T`, `f` and coordinate `Cc`/`Tc`/`fc` are used throughout.
- `Instance N rows` keeps the source row count independent of the leaf count `m`.
- The SourceSize dimensions are `c + s = 2h ≤ 2J = n`, with `hdim`, `hD` and `hsmall` derived.
- HC46 is discharged through the original `original_HC46_exact`, applied at `hEven := hsplit`.
- The caller-chosen dyadic `k ≥ 4m` is supported in the dyadic exports.
- The height, rank and dimension guards (`hsel`, `hA`, `hrd`) are retained.
- The actual append experiment is unchanged: shared uniform base, `m` unconditional appended draws, exact Grassmann β.
- There is no uniform or rank-one surrogate, and the source/star family is not narrowed.

Generic body selection being complete is distinct from the mathematical obligations around pre-draw source selection, selectors and global tables. Those obligations are still open. Selected upstream native profiles are not CMMSA bridges.

## 7. Findings

| ID | Severity | Declarations | Disposition and action |
|---|---|---|---|
| F97-1 | Verified | `same_range_right_orbit` | Sound, and general enough for deficient inputs. |
| F97-2 | Verified / closes N-2, N3, F3 | `hc46_contract_iff`, `spectral47_contract_iff` | Exact `Iff.rfl`. No construction claim. |
| F97-3 | Medium (open) | Spectral47 bridge chain | The orbit theorem is one abstract step. Still needed: a matrix-form corollary (`toMatrix'` with `U·V = V·U = 1`), character covariance, Fourier constancy on classes, append restriction to `[Y\|0]`, the orbit-count ratio, the Parseval energy bridge, then universal Spectral47 at the actual append operator, plus a fidelity audit against manuscript 4.7 (the contract uses none of `rho`, `hc`, `hs`, `hHeight`). |
| F97-4 | Low (naming) | `BinaryMatrixSameRangeOrbit` | The statement does not involve `BinaryMatrix`. Do not cite it as a matrix-action result. |
| F97-5 | Info | New roots | Not consumed by any material export. `hSpectral` is still a premise. |
| F97-6 | Info (custody) | Typed identities | Matched; legacy field labelled. Recompute from custody during fresh-checkout replay. |
| Carried | Medium (open) | Numeric NO, joint witness, source/star | As in Full95 (N-7, S2, F2, S3). |
| Carried | **HIGH (open, outside scope)** | R14 | Encoded reduction and runtime. Parameter size alone neither proves nor disproves it. Bars overall GO. |
| Carried | Low | Stale banners, old m-coupled roots, warnings | Unchanged. Inherited total warning debt is explicit, even though owned and regression gates are 0. |

## 8. Safe conditional claim

This rests on pinned kernel and Init/Mathlib/Batteries trust, the Full97 qualified receipts (184 standard profiles, seven zero exits), the typed source/object identities, and identity reuse of 323 prior bodies.

> The Full95 material claims stand unchanged. In addition:
> - Any two linear maps from a finite-dimensional `ZMod 2`-module with equal range differ by a precomposed linear automorphism, with no rank hypothesis.
> - The legacy and SourceSize HC46 and Spectral47 contracts are definitionally the same proposition, the latter for every cutoff.

**Not claimed:**
- the matrix-action, Fourier, cardinality or append-energy bridges;
- universal Spectral47 or its fidelity to manuscript 4.7;
- useful `e`/`hfail`/numeric NO;
- joint source/selector/copies/U/A witnesses;
- source/star/robust8S or the pre-draw global table;
- the physical sampler;
- encoded runtime, reduction or learning;
- upstream CMMSA bridges;
- zero total warnings or a fresh checkout;
- novelty, priority, citations, PDF or publication;
- unconditional material or manuscript acceptance.

## Remaining to-do

1. A matrix corollary of `same_range_right_orbit`: same `range (toLin' Y)` ⇒ an invertible pair `U, V` with `Y' = Y·U`.
2. Character transport and Fourier-coefficient constancy for `basisInv` functions; the append restriction to `[Y|0]`; the orbit-count ratio; the Parseval energy bridge. Then prove universal Spectral47 for the actual append operator and transfer it through `spectral47_contract_iff`.
3. Fidelity audit of `Spectral47ExactContract` against manuscript 4.7.
4. Certified scalar consumer: choose `r`, `T` and `P`; prove ΣEᵢ ≤ 1 and the high-energy side conditions; instantiate `base` and `cutoff`; give an effective L₀. Then prove `hfail` at a useful `e` (numeric NO).
5. A joint inhabitance witness for `I`, copies, `U`, `A` and `hsel`.
6. Source/star and robust8S on the trace; the pre-draw global table; the physical sampler.
7. R14: encoded reduction and runtime proof (implicit `J`, expander tables, `rotVal` cost); learning.
8. Upstream post-audit, then the CMMSA bridges.
9. Hygiene: rename or redocument the orbit file; remove stale banners; mark the m-coupled roots as superseded; dispose of warnings and linter suppression; fresh-checkout replay with hash recomputation.
10. Manuscript fidelity, novelty and citation review, PDF render, and the final full-scope providers.
