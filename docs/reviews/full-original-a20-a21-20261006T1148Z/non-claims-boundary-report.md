# Non-claims-boundary review: original A20 and A21 (Run64 / capture64)

**Lens:** this is the non-claims-boundary lens only, given as a separate top-level review. I invoked no tools, ran no compilation, made no edits and delegated nothing. The plan-mode file and exit steps in my environment were not used, because you prohibited tool calls and pseudo tool calls.

**Self-attestation limit:** I cannot report my own CLI token or context usage. Root has to record it from CLI metadata, as the packet requires.

**Result:** nothing blocks acceptance from this lens. The proposed wording overclaims nothing, but it leaves several limits implicit. Before it is adopted, it should spell out the A16/A17/A18 scope, the trust carried over from A7, the exact formal form of the A20/A21 statements, and the review-receipt identifiers. These are listed in section 5.

## 1. What the frozen bytes actually establish

### `ActualBinaryMatrixHC46A20SquareGlobalness` (435873CF)

**`a20_three_degree_global`**
- **Premises:** only `ComplexFourierSupportedThrough D f` and `UpToActualNormSqGlobal D eps f`.
- **Influence step:** the influence premise for A18 is built inside the proof, not taken from the caller. It applies `filteredCarrierFunction_energy_le_A16` to every `(A,B,T)`, giving parameter `2^(11D²)·eps`.
- **A18 step:** it then applies `actual_A18_original_global` with `r = 3*D`.
- **Budget:** the `hscale` block shows `2^(10·D·3D)·2^(11D²) = 2^(41D²)`. This matches B in the manuscript.

**`manuscript_A20_raw_fourth_le`**
- **Premises:** the original premises plus `(A,B,T)` with `finrank A + finrank(W/B) ≤ 2D`. The cost bound is part of the statement (it ranges over restrictions), not a guard.
- **First B factor (inside A19):** the coordinate function `g` gets support through `complexAmbientAffineRestrict_supportedThrough`. It gets up-to-D B-globalness through `complexAmbientAffineRestrict_coordinate_global`, which uses the exact outer-plus-inner cost of at most 3D in `complexAmbientAffineRestrict_nested_global`. A19 is then applied to `g`.
- **Second B factor:** `hsecond` comes from `complexAmbientAffineRestrict_full_mean_le_of_actualGlobal` at cost at most 3D.
- **Exponent:** `114 + 41 + 41 = 196` appears explicitly in the `hp` block.
- **Means:** the normalized carrier mean (`a20Mean`) and the coordinate `uniformMean` are matched through the `hsum` reindexing.
- **Sign of eps:** `0 ≤ eps` is derived internally, not assumed.
- **Conclusion:** the raw fourth-moment bound is proved, not assumed.

**`manuscript_A20_actual`**
- It concludes up-to-2D actual globalness of `fun M => f M * f M` with parameter `2^(196D²)·eps²`, from the original premises only. There is no square-globalness oracle.
- Each actual restriction R is rebuilt as `liftCarrierRestriction A B T ⟨⊥,⊤,0⟩` (`hlift`), and its fibre energy is matched through `a20_raw_energy_eq_lift`.
- Squaring commutes pointwise with restriction (`complexAmbientAffineRestrict_square` holds by `rfl`).

### `ActualBinaryMatrixHC46A21DyadicMoment` (2B3FE7D9)

**`a21_dyadic_strong`**
- Every case is quantified over all `n`, `d`, `D`, `eps` and `f`.
- **p = 2:** the factor is at least 1, and `eps^0 = 1`.
- **p = 4:** this is A19 with `114 ≤ C_4 = 2800`.
- **q ≥ 4:** the induction hypothesis is applied to `g = f*f` with degree `2D` and parameter `eta = 2^(196D²)·eps²` from A20.
- **Degree factor:** it is retained as `(2D)^2`.
- **Square identities:** `a21_square_moment` and `a21_square_second` are exact identities.
- **Exponent recurrence:** checked by hand, `4C_q + 196(q/2−1) + 114 = 800q² − 302q − 82 ≤ 800q² − 200q = C_{2q}`.
- **eps power:** `1 + 2(q/2−1) = (2q)/2 − 1` is `a21_density_recurrence`.
- **Signs:** monotonicity uses the internally derived `heps` and `a21_second_nonneg`.

**`manuscript_A21_actual`**
- **Premises:** only support, up-to-D actual globalness, `2 ≤ p`, and `∃ k, p = 2^k`.
- **Proof:** it obtains `k ≠ 0` from `hp2`, then weakens `C_p ≤ 200p²` (`a21_exponent_le`).
- **Imports:** only A20 and A12; there is no A22 or Hölder bridge.

### `actual_A18_original_global` (C4513E43)

**Premises:** only original support and `OriginalActualInfluenceThrough D eps`. The conclusion is that the bound `2^(10Dr)·eps` holds for every implicit `r`.

**Induction structure:**
- **Outer and inner induction:** the outer strong induction on D generalizes over `n`, `d`, `r`, `eps` and `f`. This is needed because the derivative-coordinate functions live on different matrix spaces. The inner strong induction on r generalizes over `n`, `d`, `eps` and `f`.
- **Seed cases:** the `D = 0` and `r = 0` seeds come from the order-zero influence.
- **Exact-order restrictions:** these are handled by `actual_A17_full_parent_energy`, using:
  - the top-level source bound from the inner induction;
  - order-one derivative bounds from the outer induction applied through `original_influence_order_one_derivativeCoordinate_reduction` and `actualDerivativeCoordinate_support_drop`;
  - lower rank levels from the outer induction applied through `original_influence_rank_projection`.
- **Smaller-order restrictions:** for `Q.order ≤ r−1` the proof applies the inner induction hypothesis to the whole of `f` at `r−1`. It never picks an element from a possibly empty exact-order family.
- **Inhabited fibres:** `actual_fibre_base_mem`.

**A17 branches:** both are covered in full.
- Nonzero domain: `actual_A17_domain_branch`.
- Zero domain with positive codomain codimension: `actual_A17_codomain_branch`.
- Neither branch has a caller ambient or complement guard.

**This lens therefore finds no premise disguised as an induction hypothesis**, and no dyadic or global oracle.

## 2. How the proposed wording measures up against the evidence

| Wording element | Evidence | Assessment |
|---|---|---|
| "WITH NOTES AT THE FORMAL-STATEMENT LEVEL after three successful separate reviews" | This is one of the three lenses; nothing has been adopted yet | Acceptable only after all three terminal receipts exist; must not be backdated |
| "inspected A17/A18 dependency as consumed" | Full bodies of A17Full/Domain/Codomain, A18OriginalGlobalInduction, InductionBounds, SourceGlobal, FullFunctional* and DerivativeRankProjection are supplied | Accurate. Should add that this is **not** a standalone A13–A18 manuscript milestone, and that A16 is still accepted only as consumed |
| Prior A7/A11 and A12/A19 reuse "under actual source/lineage" | Hashes match the prior acceptances: B296A5A9, 9AAFDAD1, 47A86423, A592FF69, 5097100…, 815DEF95, E76A328E, 5B59731D | Accurate. The trust gaps those reviews left open must carry forward explicitly (see 3a) |
| Exclusion list (HC46 inhabitant, real-q A22/A23, Spectral47, reduction, runtime, learning lower bound, P vs NP, full manuscript, publication, release) | Nothing in the 221 sources proves any of these | Accurate and sufficient. Add "non-dyadic p, interpolation" explicitly (see 3c) |
| S3132 PARTIAL, S3137 INCOMPLETE; compiler/helper credit zero | Native gate `accepted: false`, `helper_credit: 0`; inherited 981 warnings unchanged | Accurate |
| 85 standard profiles | The raw85 output lists 26 (A8) + 23 (A11) + 18 (A12/A19) + 1 (A16) = 68 prior, plus 17 new (4 A20, 1 A18-global, 9 A21, 1 A17, 2 A18 helpers) = 85. All are subsets of {propext, Classical.choice, Quot.sound}; none shows sorryAx | Consistent with the "17 omitted by the old parser" provenance statement |
| Closure 217 → 221 | Exactly four new author paths (A20, A20Checks, A21, A21Checks); `authorized_owned_mutations: {}` | Consistent |
| Custody before stop | Custody verified 11:44:40Z; VM `lastStop` 04:47:05−07:00 = 11:47:05Z | Consistent |

## 3. Limits the wording must state

### (a) Inherited trust through A19 → A12 → A7
A20 and A21 depend on the whole A7 graph. That graph is reused, not re-reviewed: A7Transfer (405 KB, excerpts only), T1Transfer, WeightedPredecessor, PredecessorCount, EnergyConsumer (`actualW6Derivative_weighted_fourth_moment_le_two`), A6/DR6*, A8* and A9*.

The frozen56 reviews themselves trusted indexed kernel inputs for A6/DR6, W6/EnergyConsumer, A9InitialGraph and the predecessor counts. Those gaps now carry over to A20 and A21 as well. The wording says "reused only under lineage" but should list this inherited trust explicitly.

### (b) Excluded and unprovided imports
On the A17/A18/A20/A21 path I found no lemma consumed from the eight unprovided import groups:
- MatrixLiftNominalDomain is consumed only through `actualFibre_iff`, `ker_actualLeftMap` and `actualFibreLinearEquiv`, all of which are supplied.
- ActualMZ24HyperplaneSupport is consumed only through `exists_hyperplane_containing_of_ne_top` and `relativeCodim`, which are supplied.

These modules are still in the import closure and are trusted at kernel level only. State that explicitly; do not imply they were reviewed.

### (c) Exact formal form of A21
- Only dyadic `p = 2^k` with `k ≥ 1` is covered. There is nothing for non-dyadic integer p, real p, or interpolation.
- The moment is the normalized `lpMoment p (‖f‖)`. The power of eps is a natural-number power `p/2 − 1`, which is exact for dyadic p.
- The constant `2^(200D²p²)` is a loose envelope.
- The manuscript's recurrence quantity `A_p` is not formalized as such; only the invariant `C_p = 200p² − 100p` is.
- The manuscript's special-case argument ("ε=0 ⇒ f=0", "d=0 ⇒ constant") is **not** formalized. The zero cases are instead covered uniformly by the general proof.

### (d) Exact formal form of A20
- The raw fourth-moment bound covers only restrictions of cost at most 2D.
- Square-globalness is stated with respect to actual affine restrictions.
- The nominal-raw-system form (`UpToRawNormSqGlobal`) follows only through `actual_implies_raw` with internally derivable `eps ≥ 0`. Nothing beyond this is claimed.

### (e) Manuscript correspondence is at statement level only
The formal A18 proof handles smaller-order restrictions differently from the manuscript text. The text says "smaller-order top restrictions satisfy K/4"; the Lean proof uses the inner induction hypothesis on the whole function. Both are valid, but the wording should not claim the manuscript proof text was verified line by line.

### (f) Tooling options
- `manuscript_A20_raw_fourth_le` is elaborated under `set_option backward.isDefEq.respectTransparency false`.
- `A17DomainFrequencyCovariance` uses `diagnostics true` and raises `maxHeartbeats`.

These affect elaboration only; the kernel still re-checks the declarations. They are low severity but should be disclosed.

### (g) Mathlib is library trust
Mathlib is covered only by excerpts of pinned package bytes. It is library trust, not independent review.

## 4. Severity

- **Blocking:** none.
- **Medium (wording must change before adoption):**
  - 3a: inherited A7 indexed-kernel trust is not carried forward explicitly.
  - Missing explicit "no standalone A13–A18 milestone; A16 still accepted only as consumed" in the proposed wording itself.
  - The review-receipt identifiers in 5.5 are missing.
- **Low:** 3b, 3c, 3d, 3e, 3f and 3g.

## 5. Recommended wording amendments

1. Add: "A17 and A18 (including `actual_A18_original_global` for all r) were inspected as consumed by A20 (r = 3D). This is not standalone acceptance of manuscript A13–A18. A16 remains accepted only as consumed by A19 and A20."
2. Add: "A20 and A21 inherit the unreviewed indexed-kernel trust of the frozen56 A7 lineage (A6/DR6, W6 EnergyConsumer, A9InitialGraph, predecessor counts). The eight unprovided import groups and 93 excluded bodies are kernel-trusted only."
3. Add: "A21 covers only dyadic p ≥ 2, as the normalized `lpMoment` of ‖f‖ with a loose constant. There is no non-dyadic or real-p moment and no interpolation. The manuscript's ε=0 and d=0 case argument is not formalized; those cases are covered uniformly."
4. Add: "A20 square-globalness is stated with respect to actual affine restrictions of order at most 2D."
5. Record:
   - the packet SHA and the per-lens input/stdout hashes;
   - the actual CLI model and usage for each lens;
   - an acceptance date after all three terminal receipts. The A12/A19 closeout sentence "no A20/A21 follows" is superseded only from that date, not retroactively.

GO-WITH-NOTES
