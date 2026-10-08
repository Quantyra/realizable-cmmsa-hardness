# Partition 9/9 review: matrix-lift normal form, nominal domain and direct comparison

**Verdict: GO-WITH-NOTES for this partition only.** This is not a verdict on the whole campaign.

I reviewed only the text you pasted. I used no tools, so I did not read the source index, recompute the SHA256 hashes, or compile anything. Where I say something compiles or carries an axiom profile, that rests on your GCP claims (seven zero exits, 172 standard axiom profiles), not on my own check. I cite by declaration name; line numbers are given only where I could count them reliably.

## File inventory

| File | SHA256 (as supplied, not recomputed) | Status |
|---|---|---|
| `MatrixLiftLeftRowNormalForm.lean` | 6A76…9573 | **Inspected in full**, every declaration body |
| `MatrixLiftNominalDirectComparison.lean` | E8C4…2E07 | **Inspected in full**, every declaration body |
| `MatrixLiftNominalDomain.lean` | 2463…F308 | **Inspected in full**, every declaration body |

No body was skipped. None of the three files contains `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `implemented_by` or `unsafe`.

## Proof chain checked

**Main theorem: `exact_zoom_implies_nominal_pseudorandom`.** It assumes `r < d`, `0 ≤ e` and `ExactBudgetZoomBound r d (grassIndicator g) e`. It concludes `PseudorandomExact r (2*e) (rankImageBoolean g)`. The reasoning runs from the Grassmann zoom bound to the matrix-fibre density bound, which is the right direction.

1. **Domain split** (`nominal_domain_setup`, `fixed_free_dimension`): choose `a + k = d` from a complement of `domainFixed`. Correct.
2. **Dependent fixed columns** (`density_zero_of_fixed_dependent`): every matrix in the fibre is then rank-deficient, so the density is 0 and `0 ≤ 2e` holds. This uses `he`, which is in context for `positivity`. Correct.
3. **Strict row bound** (`raw_left_rows_lt_free`): from `a + b ≤ budget = r < d = a + k` we get `b < k`. The arithmetic is sound.
4. **Budget transfer** (`join_zeroKernel_codim_le_rows`): `ker X ≤ zeroKernel ≤ Q ⊔ H`, so `codim W ≤ rank X ≤ b`. Combined with `horder` this gives `a + codim W ≤ r`. Sound, including the ℕ-subtraction in `omega`.
5. **Factor-2 comparison** (`fixed_residual_score_cross`, `fixed_residual_mean_le_two`):
   - Full-rank targets all have the same score (`fullRank_target_score_eq`). This needs no surjectivity of `Y`, which is right: an invertible column action preserves both the fibre and the span.
   - `binary_target_half` needs `targetRank < k`, which comes from `targetRank_le` and `b < k`. The number is right: the fraction of full-rank r×k matrices is at least `1 − (2^r − 1)/2^k`, which is greater than 1/2 when r < k.
   - Card factorisation (`fixed_residual_card_factor`) correctly uses `residualRowsFin_surjective`, which needs `hX`.
   - The division step is valid because the fibre card is positive, derived from `freeCard > 0` via the factorisation.
6. **Fibre bijections** (`rawNormalizedEquiv`, `fixedPartEquiv`, `fixedTargetEquiv`, `freeTargetColumnsEquiv`, `actualFibreLinearEquiv`, `rawFibreColumnsEquiv`): each is a genuine bijection. In `fixedTargetEquiv`, preserving the left equations under the inverse is checked correctly, as `X(T p₁ + N p₂) = X(T(p₁ + p₂))`.
7. **Score identity** (`extensionTest_eq_rank_image_score`, `raw_fibre_extensionTest_eq_rank_image_score`): rank-deficient matrices score 0, and full-rank matrices score `g(range)`. Every matrix in the fibre shares the anchor frame (`hanchor`). Correct.

**Hypotheses and vacuity:**
- No `hHC` premise appears in any signature in these files.
- No hypothesis is contradictory.
- `hX` is discharged by `actualLeftMap_surjective`.
- `hbk`, `hbudget` and `hrd` are derived, not assumed, inside the main theorem.
- The only unproved inputs to the main theorem are `hrd`, `he` and `hexact`.

## Findings

All findings are notes or integration questions. I found no defects.

| # | Declaration | Severity | Finding |
|---|---|---|---|
| F1 | `exact_zoom_implies_nominal_pseudorandom` (`hR` usage) | Note / integration | `by rw [hR]` closes the goal `R.budget ≤ r`, so `hR` must be the equality `R.budget = r`. That means `PseudorandomExact` covers only restrictions with budget **exactly** `r`. A consumer that needs every budget up to `r` needs a separate monotonicity argument, which is cross-partition. |
| F2 | same | Note / integration | The proof only ever establishes `R.density ≤ 2e`, an upper bound. If `PseudorandomExact` (defined outside this partition) or its consumer expects a two-sided bound, there is a mismatch. Integration should check the definition. |
| F3 | same | Note | The constant loss is exactly ×2. Downstream exponent and parameter bookkeeping must use `2e`, not `e`. |
| F4 | `rankImageBoolean`, `matrixRankImageScore` | Note | Rank-deficient matrices are scored `false`/0. That makes an upper bound easier. It is valid only if the consumer's predicate also vanishes on rank-deficient matrices. If `d > n`, the conclusion is trivially density 0. |
| F5 | `hexact : ExactBudgetZoomBound …` | Integration | The result is conditional on this bound. Whether it can hold with a useful (small) `e` for HC46/A22 is not decided here. |
| F6 | `nominal_score_mean_eq_raw_dim`, `rank_image_score_fixedPart`, `nominal_score_mean_eq_raw_dim`'s `hd ▸ g` transport | Info | I saw no use of these within the partition; they may be dead or used elsewhere. No soundness impact. |
| F7 | Many `rfl` / `change` / `simp [defn]` steps (`rawNormalized_score_eq`, `normalizedResidual_score_sum_eq`, `rawFibreColumnsEquiv_apply`, `rawFibreColumnsEquiv`'s type relying on `(actualOfRaw R T).base ≡ T`) | Info / external | These depend on the unfolding of definitions outside this partition: `liftScore`, `rowTarget`, `extensionTest`, `concatenate`, `columnLinear`, `actualLeftMap`, `actualOfRaw`. That holds only if the GCP compile claim is accepted. |
| F8 | `set_option maxHeartbeats 100000` (DirectComparison, line 13) | Info | This is stricter than the default, so it is no concern. |

## HC46 / A22 scope

These three files contain **no** HC46 or A22 declarations, and no `eta` or `q` parameters. I therefore cannot confirm from this partition that the original unrestricted-eta HC46 and real-q A22 use this same consumer. What I can confirm is that this layer adds no extra premise: in particular there is no `hHC`, and no restriction on eta or q.

## Open questions for integration

1. **Definitions to check:** `PseudorandomExact` (exact budget? one-sided?) and `ExactBudgetZoomBound`. The main questions are F1, F2 and F5.
2. **The `AffineRestriction` boundary:** check `actualOfRaw_fibre` and `actualOfRaw_order_le_budget`. A general affine constraint on matrix entries (for example a trace-like one) does not fit the "fixed domain columns plus a codomain-quotient map" normal form. So check that `AffineRestriction` is the intended restriction class and that `budget` is the intended cost measure.
3. **External lemmas whose statements I took on trust:**
   - `MatrixLiftFullRowRankBridge.binary_target_half`
   - `fullRank_target_score_eq`
   - `sum_over_actual_targets`
   - `card_freeColumns_eq_card_targets_mul_fibre`
   - `homogeneous_lift_density_of_exact_r`
   - `liftScore_eq_homLiftTest`
   - `flatten` / `span_flatten`
   - the `targetScoreSum_nonneg` lemmas
4. **HC46/A22 consumer linkage:** how this lemma feeds HC46 and A22, and how the ×2 loss and the exact-budget limit propagate.
5. **Library trust:** Init, Mathlib and Batteries are trusted through pinned sources, not reviewed here. The other open areas you listed (Spectral47, source/star/robust8S/numericNO/encoded reduction/runtime/learning, upstream bridges, manuscript/render/novelty) stay open and are outside this partition.

**Verdict: GO-WITH-NOTES.** All three files were inspected in full and I found no soundness, vacuity, quantifier or direction defects. The result is conditional on `hexact` and on the external definitions above (F1–F5).
