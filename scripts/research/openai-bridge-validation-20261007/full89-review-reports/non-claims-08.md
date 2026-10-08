# Non-claims review, Partition 8/9: Full89 A1/A14/A15 typed carriers, Grassmann counting and matrix lift

**Scope.** This review covers only this partition of Full89, not the campaign. I read only the supplied text and used no tools, so I wrote nothing. I did not recompute the SHA256 hashes, did not open `source-index.json`, and did not run Lean. Whether each tactic step is valid rests on the supplied GCP evidence: seven zero exits, standard axiom profiles, and zero unresolved trace nodes. I did not reproduce that evidence.

**Verdict: GO-WITH-NOTES.** I read every one of the 45 supplied files in full, including all bodies. I found nothing at NO-GO level. The notes below are for integration.

## File inventory (all 45 inspected; none skipped)

| # | File | Status |
|---|---|---|
| 1–5 | BinaryMatrixA1Complex, A1Composition, A1NestedCarrier, A1Phase, A1TypedFourier | inspected |
| 6–7 | BinaryMatrixActualAffine, ActualAffineCarrier | inspected |
| 8–11 | BinaryMatrixCodomainA14, CodomainA15, ComplexA14, ComplexA15 | inspected |
| 12–17 | BinaryMatrixFirstDerivative, Fourier, HybridSelector, LineA14, LineA15, LineTranslation | inspected |
| 18 | BinaryMatrixNestedSelectorA1 | inspected |
| 19–24 | BinaryMatrixTypedA14FixedBase, TypedA14Hyperplane, TypedA14HyperplaneFixedBase, TypedA14HyperplaneReduced, TypedA14Line, TypedA14Reduced | inspected |
| 25–33 | BinaryMatrixTypedA15AdaptedGlobal, TypedA15Hyperplane, TypedA15HyperplaneGlobal, TypedA15HyperplaneReduced, TypedA15HyperplaneReducedGlobal, TypedA15OneStep, TypedA15Reduced, TypedA15ReducedGlobal, TypedA15Transport | inspected |
| 34–35 | BinaryMatrixTypedHyperplaneIntrinsicP, TypedHyperplaneSelector | inspected |
| 36–37 | GrassmannCounting, GrassmannFlagPosterior | inspected |
| 38–45 | MatrixFullRowRankHalf, MatrixGrassmannFibre, MatrixGrassmannIncidence, MatrixGrassmannIntersectingAnchor, MatrixGrassmannMoment, MatrixLiftAffineTarget, MatrixLiftExactBudgetZoom, MatrixLiftFullRowRankBridge | inspected |

## What checks out

- **A1 composition** (`manuscript_A1_restrict_filter`, `manuscript_A1_complex`):
  - Both are stated for every `A₂ ≤ A₁`, `B₁ ≤ B₂`, and arbitrary `T`, `S`, `f`, `N`.
  - `selected_nested_iff` is correct in both directions. I hand-checked the quotient range and preimage arguments.
  - The complex version is derived exactly, by splitting into real and imaginary parts.
- **A13/A14 multipliers** (`lineTranslationMultiplier_eq_hybrid`, `lineP_scalar_at_adjacent_rank`):
  - The multiplier is 0 when the frequency is selected and 2^{−rank} otherwise.
  - So P gives 1 on selected frequencies of rank j or j+1 and 0 on unselected ones. Both rank cases check out.
- **A14 line identity** (`rankProjection_rawRestrict_lineP_eq_hybridDerivative`):
  - It projects the whole restricted Fourier expansion, so frequencies that collide after restriction are added together rather than assumed disjoint.
  - It holds for every `j`, including `j = 0`.
- **Typed A14 statements** (`typed_A14_fixedLine`, `typed_A14_fixedHyperplane`) are basis-independent even though the proofs use chosen complements:
  - Over GF(2), the unique nonzero vector of `L` fixes the line average and selector.
  - `typedHyperplaneSelected_iff_ker_le` proves the hyperplane selector is the intrinsic condition `ker Y ≤ H`.
- **A15 exponent:**
  - Each I−aE step costs a factor 2(1+a²).
  - With b = 2a, (1+a²)(1+b²) ≤ 4a²b² = b⁴ = 2^{4(k+1)}, which gives the 4·2^{4(k+1)}·ε bound.
  - Direction is correct: the order-(k+1) premise gives the order-k conclusion, and lifting a restriction costs exactly one extra equation.
- **Actual vs raw restrictions** (`actualOfRaw_fibre`, `rawOfActual_fibre`):
  - The conversion is exact in both directions.
  - Empty raw fibres are handled through `hε : 0 ≤ ε`, which is a satisfiable premise.
- **Matrix lift:**
  - The modular-law identity, the rank-transfer argument, and the constant fibre count `∏(2^{z+k}−2^{z+i})` are correct.
  - The factor-two argument (equal scores on all full-rank targets, more than half the targets full-rank, `g ≥ 0`) is correct.
  - `full_row_rank_gt_half` (c < k) is correct, and `smaller_budget_of_exact_r` gets its budget arithmetic right, including natural-number subtraction.
- **Vacuity:** every premise I checked is satisfiable:
  - `hL : finrank L = 1`
  - `hH : finrank (B⧸H) = 1`
  - `hε`
  - `ExactBudgetZoomBound`
  - `r < q+k`
  - `hpos`

  `hhalf` is not left as a premise: it is discharged in `MatrixLiftFullRowRankBridge`.
- **Forbidden constructs:** none in the supplied text: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, and no hHC premise.

## Findings

| ID | Severity | Location | Finding |
|---|---|---|---|
| F1 | MEDIUM (premise fidelity, for integration) | `BinaryMatrixFourier.PseudorandomExact`, `exactWholeRestriction`, `binary_hc_rankZero_exact`, `binary_hc_rankLevel_L2_exact` | "Exact budget r" here counts raw equations, zero equations included, so the whole space counts as budget r. That makes `PseudorandomExact r` effectively the "up to r" premise. It is strictly stronger than an exact actual-codimension-r premise. By contrast, `MatrixLiftExactBudgetZoom.ExactBudgetZoomBound` uses exact actual dimensions and earns the smaller-budget case through flag averaging (with `r < d`). This is not unsound locally, because a stronger hypothesis only weakens the result. But integration must check that no consumer discharges `PseudorandomExact` from a manuscript exact-r assumption, and which notion the A22/HC46 consumer uses. |
| F2 | MEDIUM (provenance) | Line 1 of `GrassmannCounting` and `GrassmannFlagPosterior`; top docstrings of `MatrixGrassmannIncidence`, `MatrixGrassmannMoment`, `MatrixGrassmannFibre` | Banners say "UNCOMPILED / SOURCE DRAFT / awaits compilation". These files are imported, directly or transitively, by `MatrixLiftExactBudgetZoom` and `MatrixLiftAffineTarget`, so they must sit inside the claimed compiled 319-file closure. Either the banners are stale or the closure claim needs checking. Integration should confirm their membership and evidence against the source index. |
| F3 | LOW | `GrassmannCounting`, `GrassmannFlagPosterior` (e.g. `frameFinite`, `gaussian_of_lt (h : n < a)`, `upperQuotientEquiv`, `Draw J`) | These two files leave out `set_option autoImplicit false` and depend on auto-bound variables (`a`, `d`, `n`, `J`); every other file disables auto-binding. In the declarations I checked this only makes statements more general, but it relies on how the project config sets auto-binding. |
| F4 | LOW (auditability) | `MatrixLiftFullRowRankBridge.binary_affine_target_*` (3 decls) | These are `def`s with no written type, and `linter.defProp` is turned off. Their statement is whatever the `@…natCard` term elaborates to. I checked it matches the parent lemma with `hhalf` filled in, but the statement is not visible in the source. |
| F5 | INFO | `MatrixGrassmannIncidence`, `MatrixGrassmannFibre`: `set_option backward.isDefEq.respectTransparency false` | This relaxes a definitional-equality setting in the elaborator. The kernel still re-checks the proofs, and the standard axiom profile covers soundness. |
| F6 | INFO | `typedHyperplaneP`, `typedLineP` | These are defined through chosen complements (`Classical.choose`). `intrinsicHyperplaneP_eq_typed` is proved only for `ψ = hyperplaneDefiningFunctional`. Over GF(2) any ψ with kernel H is unique, but the partition has no lemma saying so. A consumer quantifying over arbitrary ψ would need one. |
| F7 | INFO | `BinaryMatrixTypedA15Hyperplane`, last line | Ends with `end BinaryMatrixTypedA15Hyperplane` instead of the full namespace name. Cosmetic. |
| F8 | INFO | `lineP` docstring | `lineP j` is the manuscript's `P_{j+1}`, so A15 at k uses `lineP k`. The index is consistent but easy to misread. |
| F9 | INFO | `MatrixFullRowRankHalf.columnLinear` vs `MatrixLiftAffineTarget.columnLinear` | Two definitions with the same body. They are defeq, and the bridge goes through `Nat.card` on purpose. |

## Conditional vs universal

- **Universal:**
  - The A1, A13 and A14 identities.
  - The A15 inequalities (premise: globalness and `ε ≥ 0`).
  - The actual↔raw and typed↔coordinate equivalences.
  - `full_row_rank_gt_half` (c < k).
- **Conditional:**
  - `eventPosterior_eq_conditional`: requires `hpos`, `a ≤ d ≤ J`.
  - `homogeneous_lift_density_*`: requires the zoom/exact-r premise, `r < q+k`, and the budget condition.
  - `affine_target_*`: requires `X₁` surjective, `B` full rank, and `g ≥ 0`.

## Open for integration

1. **Imports outside this partition, not reviewed here:** `BinaryMatrixA1CoefficientTransfer`, `BinaryMatrixA1CharacterBridge`, `GrassmannIncidence`, `TripleRestrictionRank`, `VectorAdvice`. Notably, `nextDerivative_eq_restrict_hybridFilter` is `rfl`, so its content depends on definitions in CoefficientTransfer.
2. **A22/HC46 not checkable here.** The original unrestricted-eta HC46 and real-q A22 statements, and their selected consumer, are not in this partition. All I can confirm is that no declaration here adds an hHC premise.
3. **Unverified inputs.** I did not check the hashes, the 170-file selection, or the exact list of 172 theorems against `source-index.json`.
4. **Manuscript fidelity is still open.** That covers the `Selected` predicate, the E average, the P polynomial, the order and budget notions (see F1), and A15 as stated with squared norms.
5. **External library trust.** The Init/Mathlib/Batteries lemmas used, such as `LinearMap.trace_comp_comm'`, `card_linearIndependent`, `Matrix.card_GL_field` and `range_dualMap_eq_dualAnnihilator_ker`, are taken as pinned library results, not reviewed here.
