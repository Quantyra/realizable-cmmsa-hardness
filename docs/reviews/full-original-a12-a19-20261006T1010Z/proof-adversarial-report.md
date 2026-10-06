# Proof-adversarial review: original A12 / A19 (capture59)

**Lens:** proof-adversarial only. This is a separate top-level review; no other lens verdict is combined here.

**Inputs used:** the supplied packet only. I made no tool calls, edits, compilations or pseudo-tool invocations. Plan mode is active, but you explicitly prohibited tool use, so this report is the full deliverable.

**Sources inspected in full:**
- `ActualBinaryMatrixHC46A12InfluenceBound.lean` (9AAFDAD1)
- `…A12InfluenceBoundChecks.lean` (47A8642…)
- `…A12FourthMoment.lean` (5097100…)
- `ActualTypedABFullA16Final.lean` (A592FF6…), `…FullA16Assembly.lean` (BECC638…)
- The canonical flag, projection, collapse, endpoint, bottom/top and ranked-tower chain
- The A14/A15 and A1 sources
- `A11WeightedAggregate.lean` (B296A5A9)
- `A7HybridW6Transport.lean` (815DEF95)
- The A7Transfer excerpts
- paper/body.tex lines 1334–1504

---

## 1. Statement correspondence

### `manuscript_A12_actual` (A12InfluenceBound:283)

- **Hypotheses:** exactly `ComplexFourierSupportedThrough D f` and `OriginalActualInfluenceThrough D eta f`. There is nothing else:
  - no Q oracle, induction premise, `0 ≤ eta`, `eta ≤ 1`, `0 < D`, or width guard;
  - no complement or projection argument;
  - no Boolean structure.
- **Quantifiers:** implicit over all `n d D eta` and all complex `f`.
- **Conclusion:** `uniformMean |f|⁴ ≤ 2^(103·D²)·eta·uniformMean |f|²`, which matches (A12).
- **Fourth moment:** it is genuine, `Complex.normSq (f M) ^ 2`.
- **Second moment:** `uniformMean normSq` = ‖f‖₂².

### `OriginalActualInfluenceThrough` (A18OriginalGlobalInduction, definition near the top)

- It ranges over all `A, B` and every linear base `T : V d →ₗ W n`, gated by `finrank A + finrank (W ⧸ B) ≤ D`.
- The quantity is the full normalized `carrierMean` over `Hom(V/A, B)` of `|filteredCarrierFunction A B T f M|²`.
- `filteredCarrierFunction` (CanonicalDCollapse) is the hybrid filter followed by `toMatrix'(T + j_B ∘ M ∘ q_A)`.
- `Selected` (NestedSelectorA1) is `A ≤ range Y ∧ Y⁻¹(A) ≤ B` on `Yᵀ : W → V`. This is the manuscript selector and order.

### `manuscript_A19_actual` (A12InfluenceBound:300)

- **Hypotheses:** only support and `UpToActualNormSqGlobal D eps f`. There is no extra influence premise and no `eps` sign or size guard.
- **Globalness definition** (`BinaryMatrixComplexA15`) quantifies every `ActualAffineRestriction` with `order ≤ D`, at every base.
  - This includes order zero.
  - `fibreEnergy` is normalized by `fibre.card`.
  - The fibre always contains `base`, so the denominator is never zero.
- **Conclusion:** exponent 114, matching (A19).

### Name resolution

Every definition occurring in either final statement is supplied in full:

| Definition | Source |
|---|---|
| `uniformMean`, `character`, `pairing` | BinaryMatrixFourier |
| `complexFourierCoeff`, hybrid filter, affine restrict | A1Complex |
| `carrierMean` | A1TypedFourier |
| `ComplexFourierSupportedThrough` | FiniteDegreeFourierReconstruction |
| `ActualAffineRestriction`, `order`, `fibre` | ActualAffine |
| `fibreEnergy`, `UpToActualNormSqGlobal` | ComplexA15 |

The same `hsupport` and `hglobal` terms are passed to `manuscript_A7_actual` and `filteredCarrierFunction_energy_le_A16`. This forces identical constants across modules, so no shadowed homonym can intervene.

---

## 2. Selected pairs, flags and the count

**Correspondence (`a12SelectedToFlag` / `a12FlagToSelected`, lines 42–99).** The maps are:
- forward: `A ↦ A.comap ι_R`, `B ↦ B.map Y.rangeRestrict`;
- inverse: `C₁ ↦ C₁.map ι_R`, `C₂ ↦ C₂.comap rangeRestrict`.

The inverse yields a genuinely `Selected` pair:
- `C₁.map ι ≤ range`;
- if `Y u ∈ C₁.map ι`, then `rr u ∈ C₁ ≤ C₂`.

**Both inverse laws are proved.**
- `left_inverse` (69):
  - range inclusion: `(A.comap ι).map ι = A ⊓ range = A`, using `A ≤ range`;
  - kernel inclusion: `(B.map rr).comap rr = B` because `ker rr ≤ B`. The argument is `Y x = 0 ∈ A ⇒ x ∈ B`, which uses `Selected.2` and `A.zero_mem`.
- `right_inverse` (85): comap∘map is identity by injectivity of the subtype; map∘comap is identity by surjectivity of `rangeRestrict`.

**Rank-zero flags.** If `rank Y = 0`, then `R = ⊥` and there is exactly one flag. No exclusion is made.

**Endomorphism surjectivity (101).** The complement is chosen internally via `exists_isCompl`, and `range_projection` is a Mathlib library-trust item. No complement is supplied by the caller.

**Cardinality bound (108).** `card(Submodule R) ≤ card(End R) = 2^{r²}`, via `card_eq_pow_finrank`, `finrank_linearMap` and `ZMod.card`.

**Selected-pair count (119).** `card ≤ 2^{2·rank²}`. The rank identification is `a7_transpose_finrank`, with its type ascribed explicitly.

**Bound against `D` (236).** When `rank ≤ D`, `2r² ≤ 3D²`. When `rank > D`, the coefficient is zero.

This is the actual selected-pair count of each single frequency `Y`. It is not the DR6 three-frequency count. Lean's `2^{2j²}` is sharper than the manuscript's `2^{3j²}`.

---

## 3. All-pair `E² ≤ η·E` and above-support vanishing

**`a12_energy_square_le` (173).**
- For `cost ≤ D`: `E ≤ η` together with `E ≥ 0` gives `E·E ≤ η·E`.
- For `cost > D`: `a12_filter_zero_above_support` (149) applies. Every selected `Y` satisfies `rank ≥ cost > D` by `selected_frequency_rank_lower_bound` (A16Assembly). So the coefficient is zero, the filter is zero, and the energy is zero.

**`selected_frequency_rank_lower_bound` check.** The proof is verified in source:
- `dim R = dim range(q_A ∘ L) + dim A`;
- `ker(q_A ∘ L) ≤ B` gives `codim B ≤ dim range(q_A ∘ L)`.

**No sign of η is needed here.** The case split is pointwise for every pair and every base, so the inequality holds regardless of the sign of η.

---

## 4. Base means, Parseval and Fubini

**Fixed-carrier Parseval (`actual_affine_base_energy_eq_selected_fourier_mass`, A12FourthMoment).**
- With the carrier point `M` fixed, average over the matrix base `T`.
- The Fourier coefficient of `T ↦ filteredCarrierFunction A B T.toLin' f M` is `[Sel]·f̂(Y)·phase`, with phase in {±1} and `normSq(phase) = 1`.
- Complex Parseval is derived from the real and imaginary parts.
- The result is independent of `M`.
- The carrier average is then taken exactly by `field_simp` with `NT, NM ≠ 0`.

**Matrix base vs linear-map base (`a12_energy_mean_eq_mass`, 187).** These are identified by `a7MatrixLinEquiv = Matrix.toLin'`, which is excerpted in the packet:
- an `Equiv.sum_comp` reindex;
- a cast of the equal cardinalities;
- closing `rfl`.

Both sides are normalized means, so there is no hidden cardinality factor.

**Q bound (`a12_Q_le_influence_mass`, 204).**
1. Unfold `a7HybridQ`. Its excerpt is `Σ_{all (A,B)} typedUniformMean_T (carrierMean …)²`, which includes `(⊥, ⊤)` and degenerate pairs.
2. Apply the pointwise inequality under the normalized `T`-mean.
3. Swap the finite sums with `sum_comm`.
4. Convert the selected filter to `card(a12SelectedPairs)` with `card_subtype`.

The result is the genuine original Q, with no redefinition.

**Parameter sign (`a12_influence_parameter_nonneg`, 257).** `0 ≤ η` is derived from the pair `(⊥, ⊤, T = 0)`. Its cost is computed as 0 via `finrank_quotient_add_finrank`, so this holds at `D = 0` and for degenerate spaces. It is used only to multiply by `a12_selected_mass_bound`.

**Assembly.**
- `a12_Q_le` gives `Q ≤ 2^{3D²}·η·‖f‖₂²`.
- Combined with `manuscript_A7_actual` (`2^{100·D·D}`), `mul_le_mul_of_nonneg_left` with `positivity` gives `100·D·D + 3·D² = 103·D²` by `ring`.
- The arithmetic is exact; there is no slack factor.

---

## 5. A16 path (`filteredCarrierFunction_energy_le_A16`, A16Final:102)

**Flags.** `exists_canonical_source_flags` (CanonicalFlag) provides:
- a domain line flag `⊥ → A` of length `dim A`, obtained by reversing a full hyperplane flag of `A`;
- a codomain hyperplane flag `⊤ → B` of length `dim ⊤ − dim B`;
- certified endpoints.

`hk` identifies `l + h` with `dim A + codim B`.

**Parameter sign.** `heps` comes from `actual_source_parameter_nonneg` (A18SourceGlobal), which uses the order-zero whole-space restriction. It is derived internally.

**Zero-cost branch (`k = 0`).**
- Derives `A = ⊥` and `B = ⊤`.
- The typed bridge `actual_global_to_bottomTop_typed` (OriginalGlobalBridgeClean) is checked:
  - an explicit actual witness;
  - exact order equality via domain and codomain `finrank_map_eq` and quotient arithmetic;
  - an exact fibre-image identity;
  - normalized energy equality.
- `Q₀ = (⊥, ⊤, 0)` has fibre `univ`.
- Base `T` is moved to 0 by `zero_step_carrier_energy_mean`, an `addRight` reindex.
- Finally `eps ≤ 2^{11D²}·eps`, using `heps`.

**Below-carrier levels (`i < k`).**
- `filteredCarrierFunction_rankProjection_zero_of_below_carrier` gives exact zeros.
- The same zeros discharge both the level bound and every cross term involving that level.

**Retained levels (`k ≤ i ≤ D`).**
- `filteredCarrierFunction_rankProjection_energy_bound` takes `r = i − (h + l)`.
- The source's typed globalness at order `i` comes from the original actual globalness at `D` via `hQ.trans hi`.
- `canonical_source_rank_projection_energy` composes three steps:
  1. **Identity.** The terminal residual-rank projection equals the actual filter of `f^{=i}` (`canonical_source_rank_projection_collapse`). That collapse is built from:
     - `ranked_terminal_projection_eq_canonicalFilters`;
     - the per-step `canonical_line_successor_projection` / `canonical_hyperplane_successor_projection` (typed A14 at a fixed base);
     - `bottomTopSourceRankProjection`;
     - `canonical_source_signal_A1_collapse`, whose first step inserts the base and whose later steps use zero bases (A1 composition).
  2. **Typed Bessel contraction:** `typedComplexRankProjection_energy_le`.
  3. **Terminal energy:** `ranked_tower_terminal_energy`, with `rankedA15Loss ≤ 2^{10D²}` because `4rk + 2k² + 4k ≤ 10D²` under `r + k ≤ D`.
- The input is the globalness of the full `f`, not of its level, which matches (A15).

**Orthogonality.** `retained_rank_representation` writes each retained `g_i` as `typedComplexRankProjection A B (i − (h+l)) φ_i`, with a separate `φ_i` per level.
- `typedComplexRankProjection_cross_orthogonal` accepts distinct `f, g`. It transports to coordinates and applies `rankProjection_inner_eq_zero`, which is Parseval-derived.
- So distinct residual ranks are orthogonal even when the preimages differ.

**Reconstruction and summation.**
- `filteredCarrierFunction_reconstruct_range_of_support` uses linearity of the filter and range reconstruction under support.
- `carrierEnergy_finite_sum_of_orthogonal` gives energy additivity.
- `count_le_two_pow_sq` gives `(D+1) ≤ 2^{D²}`, including `D = 0` (where 1 ≤ 1).
- The final result is `2^{11D²}·eps`.

**A19 consumer.** The influence premise is built for every `(A, B, T)`. A16 holds for all costs, which is stronger than the manuscript's `k ≤ d`, and the gate is unused. Then `103 + 11 = 114` by `pow_add` and `ring`.

---

## 6. Findings

There are **no blocking findings.** All notes below are trust-limit or documentation items.

**N1 — Trust, low. Unsupplied helper statements on the A12 Parseval path.**
- `filteredCarrierFunction_fourier_expansion` and `complexFourierCoeff_{smul,character,finset_sum}` appear to come from `A18DerivativeRankProjection`. This file is in neither the 94 supplied sources nor the 64-file omission list.
- `a7_transpose_finrank` is not shown either, though its ascribed type is shown.
- Mitigation: these are proved equations or equalities about fully visible definitions, and the fresh profiles for all A12 declarations show only `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`).
- They do not affect the meaning of the statements.

**N2 — Trust, low. One omitted-64 file is proof-critical.**
- `ActualMZ24HyperplaneSupport` (`exists_hyperplane_containing_of_ne_top`, `relativeCodim`, `relativeCodim_eq_finrank_sub`) is used in `CanonicalFlag` to construct the A16 flags.
- Mitigation:
  - it is only internal to the proof;
  - the codimension-one facts are re-derived in visible code;
  - the A16 consumer profile is standard-axiom.
- No omitted definition enters any final statement.
- I found no other omitted file on the A12, A16 or A19 path.
- Record it as "kernel-trusted, not reviewed" rather than "irrelevant".

**N3 — Lineage, low. Manuscript definitions of Q, I_{A,B,T} and D_{A,B,T} lie outside the paper excerpt (lines 1334–1504).**
- Correspondence relies on the prior A7 three-lens lineage and the Root inspection of paper/body.tex lines 933–948.
- The A7 source is the comment-only successor B296A5A9, which run59 has now natively re-checked.
- Prior acceptance is reused, not independently re-proved.

**N4 — Custody, low.** `A7HybridW6Transport` (815DEF95) supplies the `typedUniformMean` and `typedW6QComponent` used in Q. Its hash does not appear in any capture manifest or owner list shown in the packet, so I could not cross-check it here.

**N5 — Library trust.** The Mathlib items relied on are:
- `Submodule.exists_isCompl`;
- `range_projection`;
- `Module.card_eq_pow_finrank`;
- `Module.finrank_linearMap`, whose `Free`/`Finite` instances on the quotient and subtype are satisfied over the field ZMod 2.

**N6 — Strength remark, not a defect.**
- Lean's A12 count (`2^{2j²}`) is sharper than the manuscript's.
- Lean's A16 drops the manuscript's `k ≤ d` restriction, since high-cost levels vanish.
- Both remain consistent with the stated exponents.

**N7 — Non-vacuity.** Both hypotheses are satisfiable with nonzero `f`. For example, take `f ≡ 1` and `D = 0` with `eta = eps = 1`; the conclusion is tight at 1 ≤ 1.

The edge cases `eta = 0` and `eps = 0` force `‖f‖₂ = 0` through the order-zero term. This is consistent and involves no division.

**Gate-integrity notes.** The NEW59 200/215 assertion error, the KeyError repair, the inherited warning debt and the legacy RED parser audit do not touch the proof sources:
- the A12 source is 9AAF;
- the Checks file is 47A8;
- the A16Final file is A592, matching its owner identity.

These items are not discharged by this review.

---

**Verdict: GO-WITH-NOTES**
