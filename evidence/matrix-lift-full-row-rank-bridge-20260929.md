# Binary affine target matrix-lift comparison

`MatrixFullRowRankHalf.full_row_rank_gt_half` proves that more than half of
the ordered `c`-by-`k` binary row targets have full row rank for every
`c < k`, including `c = 0`. It counts the actual full-rank targets and
uses the exact product count.

`MatrixLiftFullRowRankBridge` applies that count to the actual ordered
free-column rank-image lift. Its named results have no rank-half premise:

- `binary_affine_target_score_sum_le_twice` compares the fixed full-rank
  target fibre sum with the homogeneous total.
- `binary_affine_target_mean_le_twice` proves the normalized affine mean
  is at most twice the homogeneous mean, using the exact equal-fibre
  denominator.
- `binary_affine_target_zoom_density_le_two_e` combines this with the
  arbitrary-intersection eligible-zoom homogeneous bound, yielding at
  most `2*e` for each fixed full-rank target.
- `residual_row_surjective` proves that the restriction of the nonzero
  target rows to `ker X₀` is onto when the combined rows `(X₁,X₀)` are onto.

The `Nat.card` bridge carries the count across Lean modules without
depending on the chosen finite enumeration of the full-rank subtype.
The score remains zero on rank-deficient matrices; no resampling occurs.

`lake build PvNP.RealizableHardness.MatrixLiftFullRowRankBridgeChecks`
passed 2,471 jobs. `#print axioms` on the concrete count and three
comparison results reports only `[propext, Classical.choice, Quot.sound]`.

This closes the affine-target factor-two and homogeneous eligible-zoom
comparison after normal form. The reduction of arbitrary nominal
`MU=V, XM=Y` constraints to that normal form, refinement from the
smaller-budget eligible zoom to exact budget `r`, and the fixed-`U`
robust decoder are still missing. The final numerical NO-soundness
exponent is unchanged.
