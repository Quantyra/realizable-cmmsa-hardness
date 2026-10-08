# Partition 9/9 Non-Claims Review: Full89 A22/HC46 Selected Consumer, Matrix-Lift Nominal Comparison

**Verdict: GO-WITH-NOTES.** This covers partition 9 only. It is not a verdict on the whole campaign.

## Scope and method

- I inspected all three supplied files in full, every declaration body included. Nothing was skipped.
- I did not use any tools and did not compile anything. I could not open the source index or recompute the SHA256 hashes. I reviewed the pasted text on the assumption that it matches the listed hashes; integration needs to confirm that against the source index.
- Line numbers below are approximate and counted by hand. The declaration name is the authoritative reference.
- Some definitions live in other partitions: `columnLinear`, `rowTarget`, `FreeColumns`, `liftScore`, `extensionTest`, `PseudorandomExact`, `ExactBudgetZoomBound`, `actualOfRaw`, `actualLeftMap`, `concatenate`. Where I describe what they mean, I inferred it from how these files use them. Those inferences are listed as integration questions below.

| File | Status |
|---|---|
| `lean/PvNP/RealizableHardness/MatrixLiftLeftRowNormalForm.lean` (6A76…9573) | Inspected, complete |
| `lean/PvNP/RealizableHardness/MatrixLiftNominalDirectComparison.lean` (E8C4…2E07) | Inspected, complete |
| `lean/PvNP/RealizableHardness/MatrixLiftNominalDomain.lean` (2463…F308) | Inspected, complete |

**Trust surface checks:** none of the three files contains `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `implemented_by`, `native_decide`, `decide`-by-kernel shortcuts, or global `@[simp]` or `instance` declarations. The only options set are `autoImplicit false`, a local `Classical.propDecidable` instance (standard classical logic), and `maxHeartbeats 100000` in DirectComparison. That heartbeat setting is *lower* than the default, so it does not weaken anything.

## Proof chain and what it actually establishes

The top-level result is **`exact_zoom_implies_nominal_pseudorandom`** (DirectComparison, about L421):

```
r < d → 0 ≤ e → ExactBudgetZoomBound r d (grassIndicator g) e →
PseudorandomExact r (2*e) (rankImageBoolean g)
```

- **It is conditional, not universal.** The only premises left open are `hrd`, `he` and `hexact`. Every intermediate hypothesis is actually discharged inside the proof:
  - `hX` comes from `actualLeftMap_surjective`.
  - `hbk` comes from `raw_left_rows_lt_free`.
  - `hg` holds by unfolding the 0/1 indicator.
  - `hbudget` comes from `join_zeroKernel_codim_le_rows` together with `actualOfRaw_order_le_budget`.
  - The zoom geometry comes from `exists_zoom_geometry`.
- **No hHC/HC46/eta/q premise is added.** `e` is a plain real number with `0 ≤ e`, and `g` is any Boolean function on Grass(n, d). Nothing in this partition restricts eta or q.
- **Proof direction is correct**, as a chain of three steps:
  1. The density equals the nominal score mean (`density_eq_nominal_score_mean`).
  2. That mean equals the raw left-row fibre mean (`nominal_score_mean_eq_raw`, using the fibre bijection `rawFibreColumnsEquiv`).
  3. That raw mean equals the residual mean, which is at most 2 × the residual free mean, which is at most 2e (`raw_mean_eq_residual_mean`, `fixed_residual_mean_le_two`, then `homogeneous_lift_density_of_exact_r`).
  
  When the fixed columns are dependent, the density is exactly 0 (`density_zero_of_fixed_dependent`), which is correct because every matrix in the fibre is then rank-deficient.
- **The factor 2 is checked numerically.** `fixed_residual_score_cross` relies on `binary_target_half`: the number of all k-tuples into F₂^m is less than 2 × the number of surjective ones, whenever m < k. The worst case is m = k − 1. There the fraction of surjective tuples is ∏_{j=2}^{k}(1 − 2^{−j}), which stays at or above ∏_{j≥2}(1 − 2^{−j}) ≈ 0.578 > ½. The edge case m = 0 gives 1 > ½. So the strict inequality holds and the constant 2 is honest.
- **The averaging algebra checks out**:
  - `fixed_residual_mean_le_two`: the `div_le_div_iff₀` step multiplies `hcross` by the fibre count, and the fibre count is positive because `freeCard = targetCard·fibreCard > 0`.
  - `join_zeroKernel_codim_le_rows`: ker X ≤ Q ⊔ zeroKernel, so the codimension is at most the rank of X, which is at most b. The natural-number subtraction is handled correctly by `omega`.
- **Normal form (LeftRowNormalForm):** `zeroKernel = X⁻¹(span B)`. `rawNormalizedEquiv` is a genuine bijection with an explicit inverse. `residualTargetFin_full_rank` lets the left targets be dependent or zero, as the docstring says. `targetRank_lt` correctly passes b < k through to rank < k.
- **Domain (NominalDomain):** `actualFibre_iff` is a two-sided characterisation of the fibre. `fixedPartEquiv`, `fixedTargetEquiv` and `freeTargetColumnsEquiv` are bijections with proved inverses. `extensionTest_eq_rank_image_score` handles rank-deficient matrices explicitly (they score 0).

## Findings

| # | Declaration | Severity | Finding |
|---|---|---|---|
| 1 | `exact_zoom_implies_nominal_pseudorandom` (about L421) and `PseudorandomExact` (defined in another partition) | Medium (claim boundary) | Judging from the calc target, the conclusion is a **one-sided upper bound** `R.density (rankImageBoolean g) ≤ 2*e`. It is not a two-sided bound and does not compare against the global density. Integration must confirm the definition of `PseudorandomExact` and that no prose describes this as two-sided pseudorandomness. |
| 2 | Same theorem: `hR` is used as `R.budget = r` | Medium (quantifier) | It covers only restrictions whose budget is **exactly** r and whose fibre is nonempty. Restrictions with budget below r are not covered here. Integration must show that downstream consumers either apply it at each r separately or rely on a monotonicity lemma proved elsewhere. Empty fibres are excluded by the quantifier itself, which is harmless because their density is 0. |
| 3 | Same theorem: `hrd : r < d` | Low | The regime r ≥ d is not covered. Downstream use must respect that. |
| 4 | `hexact : ExactBudgetZoomBound …` | Medium (vacuity, cross-partition) | The result is only as strong as the e for which `hexact` is actually proved. For e ≥ ½ the conclusion is trivial. Whether the original A22/HC46 consumer discharges `hexact` with a non-trivial e (and the exponent of e) cannot be checked in this partition. |
| 5 | `fixed_residual_full_rank_score_eq` calls `fullRank_target_score_eq` with no surjectivity hypothesis on Y | Low (cross-partition) | This is plausibly sound, because if Y is not surjective every full-rank fibre is empty and both sides are 0. That still needs to be confirmed against the other file's actual statement. |
| 6 | `rawNormalized_score_eq` (`rfl`, about L148, LeftRowNormalForm) and `normalizedResidualEquiv` (`Equiv.refl`) | Info | Both rely on definitional unfolding: `liftScore` must be `extensionTest` applied to the coerced columns, and `FreeColumns H k` must be `Fin k → H`, i.e. all tuples, not just independent ones. That second fact is needed for the factorisation `freeCard = targetCard·fibreCard` to make sense. The successful build implies both hold, but integration should check the definitions. |
| 7 | `rank_image_score_fixedPart`, `nominal_score_mean_eq_raw_dim`, `rawNormalized_card_eq` | Info | Not used by the main chain in this partition. These are possibly dead or exported helpers, and none of them is load-bearing. |
| 8 | `splitBasis_inl` and `splitBasis_inr` close via `simp` with `prodEquivOfIsCompl_symm_apply_left/right` | Info | The simp set looks unusual for the forward map, but it was accepted by the build you reported. I found no soundness concern. |

## Cross-partition and external-boundary questions for integration

1. The definitions and statements of `PseudorandomExact`, `ExactBudgetZoomBound`, `homogeneous_lift_density_of_exact_r`, `binary_target_half`, `fullRank_target_score_eq`, `sum_over_actual_targets` and `card_freeColumns_eq_card_targets_mul_fibre`.
2. The bridge lemmas `actualOfRaw_fibre`, `actualOfRaw_order_le_budget`, `actualLeftEquiv`, and the definition of `ActualAffineRestriction.order` (I inferred it to be dim domainFixed + dim of the codomain quotient). These lemmas carry the claim that the raw nominal fibre equals the intrinsic affine fibre.
3. How the original unrestricted-eta HC46 and real-q A22 instantiate `e`, `r` and `d`, and whether the selected consumer is literally `rankImageBoolean g`. This partition contains no reference to eta or q.
4. Hash and source-index identity, the 172 axiom profiles, and the boundaries to Init, Mathlib and Batteries. Library trust is assumed, not reviewed here.
5. The items you listed as still open stay open: Spectral47, source/star/robust8S/numericNO/encoded reduction/runtime/learning, upstream bridges, and the manuscript/render/novelty gates.

**Summary:** within partition 9, the proofs hold no hidden assumptions, every internal hypothesis is discharged, and the factor 2 is proved and numerically sound. The verdict is GO-WITH-NOTES rather than GO because of the claim-boundary notes (1, 2, 4): the result is a one-sided bound, applies only at budget exactly r, and is only as strong as whatever proves `ExactBudgetZoomBound`.
