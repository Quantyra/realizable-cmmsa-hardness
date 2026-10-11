# V3 exact append composition source update

Status: uncompiled candidate source; no native acceptance is claimed.

`ExactAppendBlockIdentity.lean` now encodes the source-level append/block path that was listed as missing in `OPERATOR-COMPOSITION-GAP-ADDENDUM.md`:

- `square_mul_block_split` splits U*V into the first-c and last-s row/column blocks using the pinned finite-sum decomposition.
- `append_mul_right_block_split` splits the actual Full107 `appendBinaryMatrix` multiplication using its qualified simp lemmas `appendBinaryMatrix_apply_castAdd` and `appendBinaryMatrix_apply_natAdd`.
- `append_inverse_block_identity` gives, for arbitrary M and unrestricted B and every paired inverse (U,V), `appendBinaryMatrix (M*R) B * V = M + (B-M*S)*C` with the exact block frames.
- Here `R = U * P.transpose`, `S = U * Q.transpose`, `A = P * V`, and `C = Q * V`, where `P` and `Q` are the first-c and last-s coordinate row selectors. These have dimensions d×c, d×s, c×d, and s×d respectively, including zero-width cases.
- `invariant_append_block_identity` applies the exact `RightInvariant` contract to that full matrix.
- `fixed_pair_append_mean_eq_phi_condition` proves the fixed-GL conditional equality by the explicit bijection `B ↦ B-M*S` on every n-by-s matrix.
- `normalized_product_mean` and `phiAverage_eq_rowConditionalMean` identify the actual independent product carrier with the nested unrestricted-B then full-row-frame normalized mean.
- `g_append_eq_phi` chains the column marginal, the pointwise translation, the inverse-bottom-row marginal, and that product-normalization identity. It contains explicit map-identification lemmas matching direct first columns and bottom inverse rows with the existing GL/selected-row maps.
- `ExactRestrictedAdjoint.lean` now includes the actual append-product mean reindex, fixed right-action sum invariance for the first statistic K, averaging over paired GL matrices, and the first-column marginal step to `gAverage`. Its target assumes invariance only of K and keeps H arbitrary.

The exact definitions are in the copied successor `ExactAppendOperatorContracts.lean`: `GPhiEquation` explicitly calls `phiAverage (s := s)`, and `PhiRankEigenEquation` is for arbitrary real F without an invariance premise. The latter's manuscript dimensions are d=c+s, so its full-row-frame carrier is nonempty. Phi author's parallel arbitrary-F character/kernel-frame result is in their active v4 source; it is not imported into this source and has not been compiled.

The next source validation is root-owned: elaborate these candidate proofs against the pinned module graph, repair exact API/tactic mismatches, then integrate phi_author's kernel/frame theorem. The v1/v2 bytes remain preserved. Root owns any build, GCP, trace, and reviews.

Remaining to-do list: root native elaboration of the v3 files; integrate phi_author's arbitrary-F eigenrelation; complete trace and review.
