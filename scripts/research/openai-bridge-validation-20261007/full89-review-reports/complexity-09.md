# Complexity review, partition 9/9: Full89 matrix-lift nominal comparison substrate

**Verdict: GO-WITH-NOTES.** This verdict covers only the three supplied files. It is not a verdict on the whole campaign.

**How I reviewed.** You said no tools, so I didn't open the source index (`source-index.json`) and didn't check the SHA256 hashes against it. Everything below comes from reading the supplied text. Line numbers are counted from that text and may be off by about ±3, so declaration names are the main reference. I didn't run any Lean code, and I relied on your statement that the GCP build had zero exits and no errors.

**HC46 / A22 scope.** None of the three files mentions HC46, unrestricted eta, real q or A22. I checked them as the nominal-comparison layer underneath the selected consumer. The main result (`exact_zoom_implies_nominal_pseudorandom`) has only three hypotheses: `hrd`, `he` and `hexact`. **There is no hHC premise and no extra assumption.** Whether HC46 and A22 actually reach this result through the same consumer has to be checked in other partitions.

## Files

| File | Status |
|---|---|
| `lean/PvNP/RealizableHardness/MatrixLiftLeftRowNormalForm.lean` (6A76…9573) | **Inspected**, every declaration body |
| `lean/PvNP/RealizableHardness/MatrixLiftNominalDirectComparison.lean` (E8C4…E032) | **Inspected**, every declaration body |
| `lean/PvNP/RealizableHardness/MatrixLiftNominalDomain.lean` (2463…F308) | **Inspected**, every declaration body |

No bodies were skipped.

## Checks

**Proof direction and quantifiers.** The chain runs the right way: an exact-zoom bound implies an upper bound on nominal density.
- `R.density = nominalScoreMean` (`density_eq_nominal_score_mean`)
- `nominalScoreMean = rawMean` (`nominal_score_mean_eq_raw`). This is an exact correspondence between matrices in the fibre and column tuples (`rawFibreColumnsEquiv`).
- `rawMean = residualMean` (`raw_mean_eq_residual_mean`)
- `residualMean ≤ 2·residualFreeMean` (`fixed_residual_mean_le_two`)
- `residualFreeMean ≤ e` (comes from `homogeneous_lift_density_of_exact_r`)

The restriction `R` is universally quantified. The witnesses `T`, `D`, the two bases and `Q, W, z, s` are built per `R` from the fibre being nonempty and from `Submodule.exists_isCompl` / `exists_zoom_geometry`. They aren't assumed.

**Both cases are covered.** If the fixed columns are dependent, `density_zero_of_fixed_dependent` shows every matrix in the fibre is rank-deficient, so the density is 0 ≤ 2e. If they are independent, the main chain above applies. Neither branch is vacuous.

**Numerical bounds:**
- **Half-rank bound.** `binary_target_half` needs `targetRank B < k`. The file gets this from `targetRank_le` (rank ≤ b) and `raw_left_rows_lt_free`: order ≤ budget = r < d = dim A + dim D, so the quotient's rank is below dim D. The bound itself is true. With m < k, the share of full-rank m×k matrices is ∏(1−2^{i−k}) ≥ 1 − (2^m−1)/2^k > 1/2. The strict inequality is correct.
- **`fixed_residual_score_cross` (≈L66).** The combination is sound. It uses targetCard·s < 2·#full·s and #full·s ≤ freeScore, which needs s ≥ 0 (`hmass`, from `hg`).
- **`join_zeroKernel_codim_le_rows`.** Correct by rank–nullity, since ker X ≤ zeroKernel ≤ Q ⊔ zeroKernel. The derived bound `hbudget : a + (dim V − w) ≤ r` follows correctly from `horder` plus this lemma. Natural-number subtraction is safe here because the lemma bounds the truncated difference.

**Divisions.** Every denominator is shown to be positive: `hfree`, `htarget`, `hfibre` and `hc`. `fibreCard > 0` follows from the card factorisation when X is surjective. So none of the results depends on Lean's x/0 = 0 convention.

## Findings

No blocking defects in the inspected bodies.

| # | Severity | Location | Finding |
|---|---|---|---|
| F1 | Note (integration) | `exact_zoom_implies_nominal_pseudorandom` (end of DirectComparison) | **The whole result depends on `ExactBudgetZoomBound r d (grassIndicator g) e`.** Nothing in this partition shows that hypothesis can be met with a useful `e`. If 2e ≥ 1 the conclusion holds trivially, since density ≤ 1. This is a conditional fact, not a universal pseudorandomness claim. |
| F2 | Note (integration) | same | `hR` is used as `rw [hR]` to turn `R.budget ≤ ·` into `≤ r`, so it is presumably `R.budget = r`. **That means `PseudorandomExact` covers only restrictions whose budget is exactly r, and only bounds density from above.** It is not two-sided, and the constant is 2e, not e. The consumer must not assume monotonicity in the budget or a two-sided bound unless that is proved elsewhere. |
| F3 | Note (cross-partition) | DirectComparison and NominalDomain | **These files depend on lemmas defined in other files that this partition didn't include:**<br>• `MatrixLiftAffineTarget`: `fullRank_target_score_eq`, `sum_over_actual_targets`, `targetScoreSum_nonneg`, `card_freeColumns_eq_card_targets_mul_fibre`, `columnLinear`, `columnLinear_basis`, `rowTarget`, `liftScore`, `liftScore_eq_homLiftTest`<br>• `MatrixLiftFullRowRankBridge`: `binary_target_half`<br>• `MatrixLiftExactBudgetZoom`: `homogeneous_lift_density_of_exact_r`, `ExactBudgetZoomBound`<br>• `BinaryMatrixActualAffine`: `actualOfRaw`, `actualOfRaw_fibre`, `actualOfRaw_order_le_budget`, `actualLeftMap`, `actualLeftEquiv`, `order`<br>• `GrassmannCounting`: `flatten`, `span_flatten`, `extensionTest`, `concatenate`<br>• `AffineRestriction.density` / `.budget` and `PseudorandomExact`<br>Their statements are taken as given here. |
| F4 | Info | `rawNormalized_score_eq` (≈L147, LeftRowNormalForm) | The proof is just `rfl`, so it relies on `liftScore` unfolding by definition to `extensionTest` on the underlying vectors. The build passed, so it holds, but it will break if `liftScore` is restated. |
| F5 | Info | `nominal_score_mean_eq_raw_dim` | Not used anywhere in this partition (the main theorem uses `cases hd` instead). Harmless. |
| F6 | Info | DirectComparison L13 | `maxHeartbeats 100000` is below the default, which makes it stricter. Harmless. |
| F7 | Info | final `positivity` (DirectComparison) | This step needs `he : 0 ≤ e` from the context. It compiled, so the hypothesis was found. |

## Open questions for integration

1. Does `ExactBudgetZoomBound` quantify universally over Q, W, H, f, s under the hypotheses `hfQ`, `hsQH`, `hW`, `hrd` and `hbudget`, and can it be met with a useful e (F1)?
2. What exactly is `PseudorandomExact`? Does the selected consumer need only an upper bound at exact budget with constant 2e (F2)?
3. Do HC46 (unrestricted eta) and A22 (real q) both reach this result through the same selected consumer without adding a premise? These files can't show that.
4. The library boundaries (Init/Mathlib/Batteries, e.g. `Submodule.exists_isCompl`, `Module.finBasis`, `prodEquivOfIsCompl`) are trusted, not newly reviewed.

The other scopes you listed as open stay open: Spectral47, source/star/robust8S/numericNO, encoded reduction, runtime/learning, upstream bridges, and the manuscript/render/novelty gates.
