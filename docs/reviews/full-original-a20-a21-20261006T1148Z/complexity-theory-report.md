# Complexity-theory lens review: original A20 square globalness and A21 all-dyadic moments, including the A17/A18 dependency

**Tooling note:** you asked for no tools and no pseudo tool calls. Plan mode wants a plan file and an `ExitPlanMode` call, but those tools aren't available in this session. I made no tool calls and wrote no plan file. This review is the whole deliverable.

**Context usage:** I can't produce a verified record of my own model or token usage from inside the response. That has to come from the CLI result metadata. Nothing here should be read as proof that the packet fit the context window.

---

## 1. Scope and the trust boundary as consumed

**Inspected in full from the supplied bodies:**
- A20 and A21: `ActualBinaryMatrixHC46A20SquareGlobalness`, `…A20SquareSupport`, `…A21DyadicMoment`.
- A18: `…A18OriginalGlobalInduction`, `…A18InductionBounds`, `…A18FullFunctionalEnergy/Bridge`, `…A18SourceGlobal`, `…A18SourceConditioning`, `…A18QuotientSamplingLaw`, `…A18Conditioning`, `…A18CodomainNormalEnergy`, `…A18Transpose*`, `…A18EnergyTriangle`, `…A18DerivativeRankProjection`.
- A17: the full `…A17*` family.
- Supporting bodies: `ActualMZ24HyperplaneSupport`, `ActualTypedABFullA16Final`, the typed/coordinate transports, the A1 composition files, and `ActualFiniteDegreeFourierProduct/Reconstruction`.

**Reused under their recorded lineage, not re-proved here:**
- `manuscript_A19_actual` and `manuscript_A12_actual` (bounded acceptance at source 9AAFDAD1).
- `manuscript_A7_actual` (frozen56, through its comment-only successors).
- `filteredCarrierFunction_energy_le_A16`: I re-read its full body here, but only as consumed (by A19 and now by `a20_three_degree_global`).

**Unprovided imports.** I checked each of the eight groups to see whether any declaration actually consumed on the A17/A18/A20/A21 path is defined there:
- `ActualMZ24GenericSubfamilyRepresentative`, `ActualMZ24ComplementRestriction`, `WeightRounding`, `PosteriorReweighting`, `MatrixGrassmannIntersectingAnchor`, `MatrixLiftFullRowRankBridge`: what the path uses (`exists_hyperplane_containing_of_ne_top`, `relativeCodim_eq_finrank_sub`, `card_contained`/`gaussian`, `grass_nonempty_of_le`, `actualFibre_iff`, `ker_actualLeftMap`, `actualFibreLinearEquiv`) is defined in supplied bodies. From these files they need only ambient definitions that the kernel checks.
- `A7EnergyConsumer`, `A8Endpoint`, `A9AmbientReindex`: these feed only the A7 lineage. A21 and A20 reach that lineage only through A12/A19.
- Conclusion: no missing body carries a consumed lemma of this milestone. Their absence is a trust limit, not a gap.

**A dependency direction worth recording.** The previously accepted A7 path (`A7HybridW6Transport`, `A7Transfer`) and A12 import helpers from `A18OriginalGlobalInduction`:
- `OriginalActualInfluenceThrough`
- `carrierCoordinateNestedHomEquiv`
- `carrierCoordinate_affineMatrix`
- `actualDerivativeCoordinate_nestedFilter`

Those helpers are now visible in a complete body, and they are definitions or exact equalities, not estimates. In particular, `OriginalActualInfluenceThrough D eps f` is the full normalized carrier mean of every filtered derivative, over every (A, B, T) with cost ≤ D. That matches the manuscript's influence definition and is not a conditional-fibre mean. This closes a visibility gap from the A12/A19 review rather than opening a new one.

## 2. A18: `actual_A18_original_global`

**Statement.** Every space (n, d), every `D`, `r`, `eps` and every complex `f` is covered. The only hypotheses are `ComplexFourierSupportedThrough D f` and `OriginalActualInfluenceThrough D eps f`. The conclusion is `UpToActualNormSqGlobal r (2^(10·D·r)·eps) f`. There is no globalness, influence, positivity or ambient premise beyond these, which matches (A18) in `body.tex`.

**Induction structure (quantifiers).**
- The outer strong induction is on `D`, generalizing `n d r eps f`. The inner strong induction is on `r`, generalizing `n d eps f`, with `D` fixed.
- `ihD` is used at a different carrier space: the coordinate space `(finrank B, finrank (V/A))` of an order-one derivative. That is legitimate only because the outer induction generalizes `n d`, and it does.
- `ihD` is also used at the lower levels `i < D` with the same `r`. `ihr` is used only at `r−1`, on `fTop` and on `f` itself.
- No inductive hypothesis is assumed at the current `(D, r)`. I found no premise of the form "desired globalness or influence" passed into a recursive call.

**Seeds.**
- `D = 0`: support 0 forces `f` constant (via `complexRankProjection_reconstruct_range_of_support` and `rankProjection_zero`). The order-0 influence seed gives `|f 0|² ≤ eps`, and the budget is `2^0·eps`. No division is involved.
- `r = 0` with `D ≥ 1`: `original_influence_zero_actual_global` shows that order 0 forces `A = ⊥` and `B = ⊤`, so the fibre is everything and the energy is the ambient mean, which is at most `eps`.
- Nonnegativity of `eps` is derived (`original_influence_parameter_nonneg`), not assumed.

**Inheritance steps.**
- `original_influence_rank_projection`: each Fourier rank layer inherits the influence bound on every (A, B, T). It does this through `actual_derivative_rank_projection_energy_le`, which uses the exact selected-rank residual identity and then typed Bessel, and is zero below the cost. It works on the same full carrier, not on a conditional fibre.
- `original_influence_order_one_derivativeCoordinate_reduction`: the coordinate nested mean equals the relative mean (`actualDerivativeCoordinate_nestedMean`, via `carrierCoordinateNestedHomEquiv`). That equals the original influence at the composed endpoint with base `T + j_B S q_A` (`original_influence_A1_composition_mean`, from `manuscript_A1_complex`). The cost is exactly additive (`relative_endpoint_cost_add`), so `1 + (D−1) ≤ D`. This is the exact normalized A1 nesting that was requested.
- Support drop: `actualDerivativeCoordinate_support_drop` gives degree `D − cost = D − 1` on the reduced carrier, and keeps colliding selected frequencies inside the coefficient sum.

**Order handling.**
- If `Q.order = r`, the A17 route is used.
- Otherwise `Q.order ≤ r−1`, and `ihr (r−1)` is applied to `f` itself. Monotonicity in `r` of `2^(10Dr)` finishes the case.
- No exact-order witness is ever chosen, so an empty exact-order family cannot be exploited. This replaces the manuscript's phrasing ("smaller-order top restrictions already satisfy K/4") with a cleaner route that gives the same conclusion.

**Numerical step (`ActualBinaryMatrixHC46A18InductionBounds`).** I checked the arithmetic independently:
- Top level, first term: `10(D−1)(r−1) + 1 ≤ 10Dr − 9` holds if and only if `D + r ≥ 2`.
- Top level, second term: `2 + 2D + 10D(r−1) ≤ 10Dr − 6` holds if and only if `D ≥ 1`.
- So the top level costs at most `9/512·K`, and `9/512 ≤ 1/4`.
- Lower levels: the ratio `2^(5r) ≥ 32` gives `Σ_{i<D} 2^(5ir) ≤ 2^(5Dr)/31`, so the squared sum is at most `K/961`.
- Combining with `(a+b)² ≤ 2a² + 2b²` gives at most `K/2 + 2K/961 ≤ K`.
- Minkowski (`a18_uniformL2_finset_sum_le`) holds for an empty index set. The `L2² = fibreEnergy` step uses the uniform measure on the fibre subtype, which is inhabited by `Q.base`. At `eps = 0`, `√0 = 0` and nothing is divided.

**Severity: none blocking.**

## 3. A17: `actual_A17_full_parent_energy`

**Hypotheses:**
- `hsource`: global through `r−1` with `η₂`.
- `hderiv`: global through `r−1` with `η₁`, for every (A, B, T) of cost exactly 1.
- `complexRankProjection D f = f`, `D ≥ 1`, `r ≥ 1`, and `P.order = r`.
- There is no ambient, complement, or nonempty-fibre premise.

**Domain-positive branch.**
- Pick a nonzero `v ∈ P.domainFixed`, and set `U = span v` with codomain ⊤ (cost 1).
- `actual_derivative_bounds_every_parent_unit_cost` uses the exact lift `lift_carrierOfParentAB_eq` and the order identity `carrierOfParentAB_order_decomp` (`1 + Q.order = r`), and specializes `hderiv` at the parent's own base.
- The average term uses `actualA18_parent_fibre_energy_le_two_inside` with `s = r−1`.
- The decomposition is `homogeneous_A13_arbitrary_line`. It is built from an adapted domain equivalence that is constructed internally (`exists_adaptedDomainEquiv`), with rank-projection and selected-filter covariance proved, not assumed.
- `actual_fibre_energy_add_smul_le` then gives `2η₁ + 2(2^D)²·2η₂`.

**Domain-zero / codomain-positive branch.**
- Order `r ≥ 1` with `A = ⊥` forces codimension `r`, so the coordinate dual annihilator is nonzero.
- From a nonzero `u` in it, the hyperplane `B = ker(e⁻¹u) ⊇ P.codomainVariation` has codimension 1.
- The A13 decomposition is transported through transpose by `complexAmbientHybridFilter_transpose_bot` and `complexTranspose_actualA18Average`. The average is bounded by `actualA18_parent_fibre_energy_le_two_codomain_normal`, using transpose globalness and `transposeActualRestriction_order_le`.
- The degenerate cases `n = 0` and `d = 0` fall to `omega` contradictions or to this branch. No guard is needed.

**The `2η` measure calculation** (`A18SourceGlobal` and `FullFunctionalEnergy`):
- The ambient `(ψ, w)` draw is reindexed by restricted functional × quotient coordinate. This is an exact bijection, `globalFunctionalRestrictionEquiv`.
- Jensen is applied in the restricted-functional coordinate. Columns are partitioned by quotient cosets of `B`:
  - the zero coset is the stable law (order ≤ `s`, bound `η ≤ 2η`);
  - every nonzero coset is the outside-column law in `B ⊔ ⟨w⟩`.
- The half-mass of the outside-column event is proved (`outsideColumn_card_half`), not assumed. The expanded order drops by 2, so the bound is `2η`.
- When `s = 0`, the expanded case is contradictory and is discharged by `omega` without a negative-order hypothesis. This matches the manuscript text after (A16).

**Inhabited fibres:** `actual_fibre_base_mem` is used wherever `card > 0` is needed. **Severity: none.**

## 4. A20

**`a20_three_degree_global`.**
- Hypotheses are support `D` and `UpToActualNormSqGlobal D eps` only.
- A16 (no cost premise) gives `OriginalActualInfluenceThrough D (2^(11D²)·eps)`.
- A18 at `r = 3D` gives scale `2^(30D²)·2^(11D²) = 2^(41D²)`. That is the first factor `B`, and the exponent identity is proved by `ring`.

**`manuscript_A20_raw_fourth_le`.**
- Setup: cost of (A, B) ≤ 2D, any `T`, and the unfiltered raw restriction `complexAmbientAffineRestrict A B T f`.
- Support: rank does not increase under quotient and subspace (`rawCarrierFrequency_rank_le`), so `complexAmbientAffineRestrict_supportedThrough` gives carrier degree ≤ D.
- Globalness of the coordinate function through D with parameter `B`: `complexAmbientAffineRestrict_coordinate_global`. It composes `typedOfCoordinate`, `complexAmbientAffineRestrict_nested_global` and `relative_endpoint_cost_add`, so the total is ≤ 2D + D = 3D.
- A19 is applied on the actual coordinate space and gives `2^(114D²)·B·second`.
- The second moment is ≤ `B` via `complexAmbientAffineRestrict_full_mean_le_of_actualGlobal` (order ≤ 2D ≤ 3D). This is the second factor `B`.
- Total: `114 + 41 + 41 = 196`.
- Normalizations: the carrier mean `a20Mean` is transported to the coordinate `uniformMean` by `Equiv.sum_comp` plus `Fintype.card_congr`. The carrier mean equals the actual fibre energy by `liftCarrierMatrix_normalizedMean`. No cardinality factor is lost.
- `budget ≥ 0` is derived from `eps ≥ 0`, which comes from `hglobal`. The fourth-moment bound is derived, not assumed.

**`manuscript_A20_square_supportedThrough`:** support `D + D`, written as `2·D`, from convolution plus rank subadditivity (`binaryMatrix_rank_add_le`).

**`manuscript_A20_actual`.**
- For an arbitrary actual restriction `R` with order ≤ 2D, set `A = R.domainFixed`, `B = R.codomainVariation`, `T = R.base.mulVecLin` and `Q = (⊥, ⊤, 0)`.
- `liftCarrierRestriction … = R` holds exactly.
- Raw restriction commutes with squaring by `rfl`, and `normSq(xy)` factors.
- So `fibreEnergy R.fibre (f·f) ≤ 2^(196D²)·eps²`. This is the actual up-to-2D globalness of `f·f`.
- There is no square-global oracle, and no guard on zero degree, zero dimension, or zero parameter.

## 5. A21: `a21_dyadic_strong` and `manuscript_A21_actual`

**Quantifiers.** The induction is on `k`, and the motive keeps `∀ {n d D eps} f`. The inductive step instantiates it at `g = f·f`, with degree `2D` and parameter `η = 2^(196D²)·eps²`, which are exactly A20's hypotheses and conclusion.

**Base case `p = 2`:** the bound is `second ≤ 2^(600D²)·second·eps⁰`, using `eps^0 = 1` (including at `eps = 0`) and `second ≥ 0`. This is a weakening by a factor of at least 1.

**`p = 4`:** A19 with `114 ≤ C_4 = 2800`.

**Step `q ≥ 4` to `2q`:**
- Evenness and `q ≥ 4` are derived internally from `q = 2^(k+1)`.
- `lpMoment (2q) |f| = lpMoment q |g|` (`a21_square_moment`), and `E|g|² = E|f|⁴` (`a21_square_second`), followed by A19.
- Exponent check: `4·C_q + 196(q/2−1) + 114 ≤ C_{2q}`. With `C_q = 200q² − 100q`, the left side is `800q² − 400q + 98q − 82` and the right side is `800q² − 200q`, a slack of `302q + 82`. The factor 4 comes from `(2D)² = 4D²`, which is retained.
- Density: `1 + 2(q/2 − 1) = q − 1 = (2q)/2 − 1` (`a21_density_recurrence`).
- Signs: `houter ≥ 0`, `η^(…) ≥ 0`, `second ≥ 0` and `eps^(…) ≥ 0`. Every inequality is a monotone multiplication by a nonnegative factor, and exponent monotonicity uses base `2 ≥ 1`.

**Final theorem.**
- `p ≥ 2` and dyadic gives `k = j+1` (derived), and `C_p·D² ≤ 200·D²·p²`.
- The statement is exactly `lpMoment p ‖f‖ ≤ 2^(200D²p²)·E|f|²·eps^(p/2−1)` for arbitrary complex `f`, all `n, d, D`, and all `eps` with `eps ≥ 0` derived. This matches (A21) in `body.tex`.
- The proof imports only A20 and A12. There is no A22, Hölder, real-`q` or interpolation bridge.

**Manuscript correspondence.** The manuscript defines `A_4 = 114` and `A_p = 4A_{p/2} + 49p − 82`. The formal proof carries the dominating envelope `200p² − 100p` directly. That is permitted bookkeeping, and the doubled degree is carried in both.

## 6. Notes (non-blocking)

| # | Note | Severity |
|---|---|---|
| N1 | The A18 non-exact-order case uses the smaller-`r` inductive hypothesis on `f` itself, not the manuscript's "K/4 for smaller-order top restrictions". The conclusion is identical, and the formal route is stronger with respect to empty exact-order families. The manuscript wording could be aligned. | Low |
| N2 | `backward.isDefEq.respectTransparency false` appears in `manuscript_A20_raw_fourth_le` (and in A11). `a20Mean` and the private `finiteUniformMean` are matched by `exact` up to unfolding. This is an elaboration setting only; the kernel still checks everything and the profiles show only standard axioms. | Info |
| N3 | Stale "UNCOMPILED companion source" headers remain in `GrassmannCounting`, `GrassmannIncidence` and `TripleRestrictionDimension`, which are consumed by `ActualMZ24HyperplaneSupport` and A16 flags. These headers contradict the GREEN receipts. Fix them only in a separate comment-only follow-up. | Low |
| N4 | The trust boundary holds: A16, A12/A19 and A7 are reused under their lineage and are not independently re-accepted. The unprovided imports carry no lemma consumed on this path (§1). Mathlib, including `exists_isCompl`, projection, `toMatrix'` and dual annihilators, is pinned library trust. | Info |
| N5 | The logical force is bounded. A21 covers integer dyadic `p` only. The constant depends on `D` alone, uniformly over dimensions. Nothing follows for real `q`, HC46 inhabitation, Spectral47, Q upper bounds without the influence premise, or any reduction or runtime claim. | Info |
| N6 | `maxHeartbeats`/`diagnostics` options in `A17DomainFrequencyCovariance` and elsewhere are performance settings only. | Info |

## 7. On the proposed acceptance wording

The wording, accepted with notes at the formal-statement level, is consistent with what this lens verified:
- The exponent and quantifier bookkeeping for (A18), (A20) and (A21) holds exactly as stated.
- No hypothesis is weaker than the original statement and no premise disguises the conclusion.
- The A17/A18 dependency was inspected in full as consumed.

This lens gives no certification beyond that, consistent with the stated non-claims (S3132 PARTIAL, S3137 INCOMPLETE, compiler credit 0).

**GO-WITH-NOTES**
