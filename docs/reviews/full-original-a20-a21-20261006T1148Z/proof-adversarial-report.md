# Proof-adversarial review: original A20/A21 with A17/A18 as consumed dependencies

**Scope.** This is a single-lens review (proof-adversarial) of the frozen packet only. I made no tool calls, ran no compiles and made no edits. I checked every claim below against the printed source bodies, cited by declaration name. Native GREEN is treated as necessary, not sufficient.

---

## 1. A21: `ActualBinaryMatrixHC46A21DyadicMoment.lean` (2B3FE7D9)

**Statement of `manuscript_A21_actual`.**
- Quantifies over arbitrary `n d D p`, `eps : Real` and complex `f`.
- Its only analytic premises are `ComplexFourierSupportedThrough D f` and `UpToActualNormSqGlobal D eps f`.
- `p` is restricted only by `2 ≤ p` and `∃ k, p = 2^k`.
- The conclusion is `lpMoment p (‖f‖) ≤ 2^(200·D²·p²) · E|f|² · eps^(p/2−1)`.
- There is no positivity guard on `D`, on `eps`, or on the dimensions.
- `eps ≥ 0` is derived internally via `filteredCarrierFunction_parameter_nonneg`, which is `actual_source_parameter_nonneg`. That lemma uses the order-0 restriction `(⊥, ⊤, 0)`, which exists at every order cutoff including 0.
- `p ≥ 2` forces `k = j+1`, so `p/2 − 1` is an exact natural number.

**`a21_dyadic_strong`.** It is proved by `induction k`. The statement after the colon is `∀ {n d D eps} f, …`, so the induction hypothesis is fully generalized over spaces, degree and parameter. The cases:

- **k = 0 (p = 2).**
  - `a21_moment_even f 1` identifies the 2-moment with E|f|².
  - The goal is rewritten to `eps^0`, which is definitionally `2/2 − 1 = 0`.
  - The factor `2^(·)` is at least 1 and multiplies the nonnegative second moment (`a21_second_nonneg`).
  - This is the "weakened by factor ≥ 1" step; it is sound.
- **k+1 = 1 (p = 4).**
  - This is the original `manuscript_A19_actual`, unchanged.
  - The constant check is `a21Exponent 4 = 3200 − 400 = 2800 ≥ 114`.
  - Monotonicity is applied with `eps · second ≥ 0`.
- **k ≥ 1 (q = 2^(k+1) ≥ 4).** The induction hypothesis is applied to `g = f·f` with:
  - degree `2D`, from `manuscript_A20_square_supportedThrough`;
  - parameter `eta = 2^(196D²)·eps²`, from `manuscript_A20_actual`.

  It is not applied to a weakened or assumed square-globalness premise. The remaining steps:
  - The exact identities are `a21_square_moment` (`‖f f‖^q = ‖f‖^(2q)`) and `a21_square_second` (`normSq(f f) = normSq(f)²`).
  - The second moment of `g`, which is E|f|⁴, is then bounded by A19 applied to `f` itself (degree `D`, parameter `eps`). That is the correct hypothesis direction.
  - The monotone substitution uses `houter ≥ 0` and `heta ≥ 0`.
- **Exponent bookkeeping.**
  - Writing C_q = 200q² − 100q, we have 4·C_q + 196(q/2 − 1) + 114 = 800q² − 302q − 82. This is at most C_{2q} = 800q² − 200q, as `a21_exponent_recurrence` states.
  - The degree factor 4 is retained explicitly through `(2D)² = 4D²` in `htotal`.
  - The density identity is 1 + 2(q/2 − 1) = 2q/2 − 1 (`a21_density_recurrence`), which needs q even and q ≥ 4; both are established internally.
  - `halgebra` applies `mul_pow`, `pow_mul` and the density identity correctly.
  - The final `pow_le_pow_right₀` uses base 2 ≥ 1 and multiplies by the nonnegative factors `second` and `eps^…`.

**Additional checks.**
- No Hölder or A22 bridge is imported or used.
- `lpMoment` is the genuine normalized moment `uniformMean |·|^p` of `‖f‖`.
- Natural subtraction appears only in `a21Exponent` and in `p/2 − 1`. In both places it is exact under the hypotheses, and `a21_exponent_le` only weakens.

**Verdict on A21: sound as stated.**

---

## 2. A20: `ActualBinaryMatrixHC46A20SquareGlobalness.lean` (435873CF) and `…A20SquareSupport.lean` (54D6D06B)

**`a20_three_degree_global`.**
- It builds `OriginalActualInfluenceThrough D (2^(11D²)eps) f` directly from `filteredCarrierFunction_energy_le_A16`. That lemma holds for every A, B and T with no cost restriction, so it is valid in particular for cost ≤ D.
- It then calls `actual_A18_original_global` with `r = 3D`.
- `hscale` evaluates the budget as 2^(10·D·3D) · 2^(11D²) = 2^(41D²), so B = 2^(41D²)·eps.
- This is a derived budget, not a caller hypothesis.

**`manuscript_A20_raw_fourth_le`.**
- `raw` is the unfiltered `complexAmbientAffineRestrict A B T f`, so it really is the raw restriction.
- **Support.** `complexAmbientAffineRestrict_supportedThrough` expands `raw` over all ambient frequencies with no Selected predicate. It then uses `rawCarrierFrequency_rank_le`: the induced carrier frequency has rank at most `Y.rank`, by factoring through `range Y` and taking a quotient. Support D is therefore preserved, and the statement is transported to coordinates by `carrierFourier_support_iff_coordinate`.
- **Globalness, via `complexAmbientAffineRestrict_coordinate_global` and then `…_typed_global` and `…_nested_global`.**
  - Each inner restriction Q of order ≤ D on the carrier is identified with the original raw restriction on the composed endpoint `(A₁₂.comap A₂.mkQ, B₁₂.map B₂.subtype)`.
  - The composed base is `T' = T + B.subtype ∘ S ∘ mkQ`.
  - The identification is exact, via `complexAmbientAffineRestrict_nested_squareMean` (the `nestedCarrierEquiv` reindexing of sum and card).
  - `relative_endpoint_cost_add` gives exact outer + inner cost addition, so the composed cost is ≤ 2D + D = 3D.
  - `hpoint` identifies the inner carrier restriction with `(carrierFibreQuotientHomEquiv Q).symm N`, which is the actual fibre `Q.base + Q.codomainVariation.subtype ∘ N ∘ mkQ`.
  - The normalized fibre mean is matched exactly (sum and card via the equivalence).
- **Second moment.** `complexAmbientAffineRestrict_full_mean_le_of_actualGlobal` lifts the full carrier to `liftCarrierRestriction A B T (⊥, ⊤, 0)`. That lift has order dim A + codim B ≤ 2D ≤ 3D, and the fibre mean is transported exactly by `liftCarrierMatrix_normalizedMean`. This gives E|raw|² ≤ B.
- **Chain.** Fourth moment ≤ 2^(114D²)·B·second ≤ 2^(114D²)·B·B = 2^(196D²)·eps².
  - Both factors of B are present: 114 + 41 + 41 = 196.
  - `hb ≥ 0` is derived.
- **Means.** `hsum` matches `uniformMean` over the coordinate matrices with `a20Mean` over the carrier via `Equiv.sum_comp` and card equality.

**`manuscript_A20_actual`.**
- For an arbitrary `R` of order ≤ 2D, `hlift` shows `liftCarrierRestriction R.domainFixed R.codomainVariation R.base.mulVecLin (⊥, ⊤, 0) = R`. This follows from `⊥.comap mkQ = A`, `⊤.map subtype = B`, and `toMatrix' ∘ toLin' = id`.
- The fibre energy of `f·f` on `R` therefore equals the carrier mean of `normSq(raw f · raw f)`. This uses `complexAmbientAffineRestrict_square` (definitional) and `normSq_mul`, which gives `normSq(raw)²`, i.e. the raw fourth moment.
- So the raw fourth-moment bound is derived, not assumed, and no square-global oracle enters.
- Square support is provided by `complexFourierSupportedThrough_mul`: the convolution identity combined with `binaryMatrix_rank_add_le`. It holds for arbitrary complex `f` with no width condition.

**Verdict on A20: sound as stated.**

---

## 3. A18: `ActualBinaryMatrixHC46A18OriginalGlobalInduction.lean` (C4513E43), newly accepted here as a consumed dependency

**Statement of `actual_A18_original_global`.**
- Its only premises are `ComplexFourierSupportedThrough D f` and `OriginalActualInfluenceThrough D eps f`.
- `OriginalActualInfluenceThrough` is defined as the full normalized `carrierMean` of `filteredCarrierFunction A B T f`, for every T and every cost ≤ D. That is the manuscript's influence, not a conditional or fibre mean.
- The conclusion holds for every `r`.

**Induction structure.**
- The outer induction is `Nat.strong_induction_on D`, generalizing `n d r eps f`.
- The inner induction is strong induction on `r`, generalizing `n d eps f`. The hypotheses dependent on `f` are reverted automatically.
- No premise of the form "desired globalness" or "derivative influence" appears in the hypotheses. Each use of an induction hypothesis is discharged from proved facts, as the cases below show.

**Base cases.**
- **D = 0.**
  - `complexRankProjection_zero_constant_of_supported_zero` shows `f` is constant.
  - `original_influence_order_zero_seed_ambient` reindexes the bottom/top carrier to the ambient matrices exactly, via `bottomTopAmbientMatrixEquiv`.
  - The fibre is nonempty because `actual_fibre_base_mem` gives the base as a member.
  - Energy is `|c|² ≤ eps`, and the budget is `2^0·eps`.
- **r = 0.**
  - `original_influence_zero_actual_global` derives `domainFixed = ⊥` and `codomainVariation = ⊤` from `order = 0`, so the fibre is `univ`.
  - The result is again the ambient seed.
  - No division is used, and the eps = 0 case is included.

**Main step (D, r ≥ 1).**
- `fTop` is `complexRankProjection D f`.
  - Its support follows from `complexRankProjection_supportedThrough`.
  - Its influence follows from `original_influence_rank_projection`, i.e. `actual_derivative_rank_projection_energy_le`.
    - When the cost is ≤ i, `filteredCarrierFunction_rankProjection_eq_typed` gives an exact residual-rank identity, and typed Parseval/Bessel bounds it.
    - When the cost is > i, the projection is zero.
  - This bound holds on the same full carrier.
- **`hsource`** is `ihr (r−1)` applied to `fTop`: same D, strictly smaller r, with proved support and influence.
- **`hderiv`**, for each cost-1 triple (A, B, T):
  - Influence through D − 1 comes from `original_influence_order_one_derivativeCoordinate_reduction`. In that lemma:
    - `actualDerivativeCoordinate_nestedMean` and `…_nestedFilter` handle the coordinate selected filter and its affine square;
    - `complexCarrierHybridFilter_coordinate` (`selected_reindex_mapped`, the coordinate frequency character) transports the selected filter;
    - `original_influence_A1_relative_mean` and `manuscript_A1_complex` handle the relative endpoint;
    - `relative_endpoint_cost_add` gives the exact cost 1 + inner ≤ D.
  - Support D − 1 comes from `actualDerivativeCoordinate_support_drop`, i.e. `selected_frequency_rank_eq_carrier_rank_add_cost`.
  - Only then is `ihD (D−1)` invoked, on the reduced carrier space.
- **Decomposition.** `complexRankProjection_reconstruct_range_of_support` gives f = fTop + Σ_{i<D} proj_i f exactly.
- **Exact order r.**
  - The top contribution is bounded by `actual_A17_full_parent_energy` (see section 4) and then by `a18_top_contribution_le_nine512`. I re-derived the exponents: 10·d₀·r₀ + 10 ≤ 10Dr, and 2D + 10D·r₀ + 8 ≤ 10Dr when D ≥ 1. Together these give 1/512 + 1/64 = 9/512 ≤ 1/4.
  - Each lower level uses `ihD i` (i < D) at the same r, with influences inherited at cost ≤ i ≤ D.
  - L² handling:
    - `a18_l2_sq_eq_fibreEnergy` uses exact normalization (card of the subtype equals card of the fibre).
    - Minkowski is `a18_uniformL2_finset_sum_le`, via `Real.Lp_add_le_of_nonneg` with p = 2. The empty index set is allowed.
    - Then (a+b)² ≤ 2a² + 2b².
  - The geometric sum Σ 2^(5ir) ≤ 2^(5Dr)/31 needs r ≥ 1.
  - In total, K/2 + 2K/961 ≤ K. The cross terms are retained.
- **Order < r.** `ihr (r−1)` is applied to the same `f`, with the monotone budget. This is the paper's "smaller-order induction, not a choice from an empty family" provision, implemented as stated.

**Verdict on A18: I verify the proof structure, constants, normalizations and hypothesis directions.**

---

## 4. A17: `…A17Full` and its branches

`actual_A17_full_parent_energy` case-splits on `P.domainFixed = ⊥`. There is no ambient guard and no complement guard.

**Domain branch.**
- A nonzero `v ∈ P.domainFixed` is chosen; it is guaranteed by `exists_mem_ne_zero_of_ne_bot`.
- **`hcomponent`.** `actual_derivative_bounds_every_parent_unit_cost` handles this term:
  - `carrierOfParentAB U ⊤ P` lifts exactly to `P` (`lift_carrierOfParentAB_eq`);
  - the cost decomposition `1 + Q.order = r` is exact;
  - so the derivative's (r−1)-globalness at base `toLin' P.base` bounds the energy of `L_U f` on `P.fibre`.
- **`haverage`.** This is `actualA18_parent_fibre_energy_le_two_inside`, the paper's E_U calculation:
  - functional/row reindexing (`globalFunctionalRestrictionEquiv`);
  - Jensen over the restricted functional, with nonemptiness from v ≠ 0;
  - mean exchange;
  - the per-functional all-columns bound, via quotient-coset partition (`quotientCoset_partition_mean_le_two`):
    - the zero coset is the stable case, with Q′ of order ≤ s;
    - nonzero cosets are the expanded case, with order ≤ s − 1, using the proved half-mass `outsideColumn_card_half` and `conditional_uniform_mean_le_two`.
  - The section coordinates are fixed once, before the coset, by `…coordinates_coe_uniform`.
  - When s = 0 the expanded case is arithmetically vacuous, so no negative-order hypothesis is used.
- **Decomposition and conclusion.**
  - `homogeneous_A13_arbitrary_line` uses an adapted equivalence built from `v` (`exists_adaptedDomainEquiv`) and covariance of the filter, the average and the rank projection. No line-compatibility premise enters.
  - The case d = 0 is vacuous.
  - `actual_fibre_energy_add_smul_le` uses a nonempty fibre and c = 2^D ≥ 0.

**Codomain branch.**
- r ≥ 1 together with domainFixed = ⊥ forces codim = r, so the dual annihilator is nonzero.
- From a nonzero element we get `B = ker φ`, with codim B = 1, `P.codomainVariation ≤ B`, and `U = span{u} = coordinateDualAnnihilator B`.
- The average is `actualA18_parent_fibre_energy_le_two_codomain_normal`, obtained from the inside lemma applied to `transposeActualRestriction P`. Its order is ≤ `P.order`, and its fibre is the image of `P.fibre` under transpose.
- The decomposition is transported through `complexAmbientHybridFilter_transpose_bot` and `complexTranspose_actualA18Average`. These are the same operators that appear in `hcomponent` and `haverage`.

**Verdict on A17: verified.**

---

## 5. Notes and severity

**N1 (Low): reused trust boundary.** A19 sits on the A7/A11 and A12 path. That path depends on excluded bodies: A7Transfer, A7EnergyConsumer, PredecessorCount, WeightedPredecessor, A6/DR6, A8/A9. These are reused only via the prior frozen56 and A12/A19 GO-WITH-NOTES reviews. I did not independently re-prove them.

**N2 (Low): lineage oddity, not a logic defect.**
- A7HybridW6Transport and A7Transfer import `A20SquareSupport` and `A18OriginalGlobalInduction`.
- The consumed helpers are `filteredCarrierFunction_supportedThrough` and `carrierCoordinateNestedHomEquiv`, `carrierCoordinateBaseLift`, `carrierCoordinate_affineMatrix`. All of these are fully supplied here and are correct as stated.
- The packet does not state whether C4513E43 or 54D6D06B equal their frozen56 bytes. A7 acceptance reuse therefore rests on these helper statements, which I re-inspected, plus the fresh Run64 kernel check.
- No logical circularity is possible: the kernel import DAG is acyclic, and no A7-path theorem calls `actual_A18_original_global`.

**N3 (Low): unprovided imports.**
- The unprovided imports are ActualMZ24ComplementRestriction, GenericSubfamilyRepresentative, MatrixLiftFullRowRankBridge, MatrixGrassmannIntersectingAnchor, WeightRounding, PosteriorReweighting, A8Endpoint, A9AmbientReindex and A7EnergyConsumer.
- None supplies a definition that appears in the statement or on the proof path of A17, A18, A20 or A21. The last three supply definitions on the reused A7/A11 path (see N1).
- Hyperplane existence (`exists_hyperplane_containing_of_ne_top`) uses only supplied GrassmannCounting, ActualMaximalPairLadder and ActualBinaryGrassmannIncidence facts.
- The standard axiom profiles exclude any injected `sorry` or axiom.

**N4 (Info): stale and inconsistent comments.**
- The A20 header reads "candidate … not certification".
- ParentFibreBridge states that "identifying … is a separate obligation"; the obligation is in fact discharged later in the same file.
- `set_option backward.isDefEq.respectTransparency false` and `diagnostics true` affect elaboration only, not the kernel.
- These comments should be refreshed in a later comment-only change.

**N5 (Info): manuscript correspondence.**
- The Lean A21 uses the stronger uniform constant C_p = 200p² − 100p. It does not use the paper's A_p recurrence or its ε = 0 / d = 0 special cases. The Lean route is stronger and division-free.
- The Lean A20 matches (A20) exactly, including the derivation of both B factors.

**N6 (Info): what this does not cover.**
- This acceptance is at formal-statement level only.
- No HC46 inhabitant, real-q A22/A23, Spectral47, reduction, runtime result, full manuscript certification or release follows from it.
- Actual CLI model and context usage must still be recorded by the operator; it is not inferable from the packet.

**Blocking findings: none.**

GO-WITH-NOTES
