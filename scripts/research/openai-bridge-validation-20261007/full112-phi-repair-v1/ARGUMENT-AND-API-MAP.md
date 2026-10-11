# Exact Phi eigenrelation candidate Full112 v1

Status: uncompiled author continuation. This is a source offer with concrete Lean proof bodies, not kernel-verified evidence. The parent compiler owner has not run this candidate through the pinned GCP compiler. The accompanying ExactPhiEigenrelationChecks.lean requests the three public signatures and #print axioms reports.

## Main results offered

Module/namespace: PvNP.RealizableHardness.ExactPhiEigenrelation.

- unrestricted_B_character_mean: for fixed C, the unrestricted independent B average of character Y (B * C) is one exactly if Y * C.transpose = 0, otherwise zero. The proof reduces the bilinear pairing to pairing (Y * C.transpose) B and invokes the captured pinned character orthogonality theorem.
- matrix_rows_kernel_iff and row_li_iff_kernel_subtype_li: matrix annihilation is equivalent to every row of C belonging to ker Y.mulVecLin; row independence is reflected across the injective kernel subtype map.
- kernelSurvivorFrameEquiv: surviving full-row-rank matrices correspond bijectively to independent ordered s-frames in ker Y.mulVecLin.
- kernelSurvivor_card: rank-nullity gives kernel dimension d - Y.rank; card_frame gives the exact count when s ≤ d - rank, and an explicit empty-frame/zero-product branch handles the impossible case. Thus the expression remains valid for s=0, d=0, and impossible dimensions.
- kernel_fraction_eq_product: derives the manuscript's s-factor eigenvalue from the captured frame-product ratio duality and product formula, under i ≤ d and s ≤ d.
- phiAverage_character_eigen and phiAverage_character_product: prove the character eigenrelation by summing first over B, then counting the kernel-surviving full-row frames, and normalizing by the exact frame count. The assumption is only s ≤ d; there is no right-invariance premise.
- phiAverage_rankProjection_eigen: distributes Phi over the finite Fourier sum and factors the common eigenvalue for every rank-i character. F is an arbitrary real-valued function; there is no right-invariance premise.

The operator interface is the already captured ExactAppendOperatorContracts.FullRowFrame, phiAverage, and BinaryMatrixFourier.rankProjection. The operator author should import this module by the namespace above and pass the explicit (s := s) argument to phiAverage.

## Captured API dependencies inspected

The proof uses the source identities in BinaryMatrixFourier (character_add_right, character_orthogonality, character_zero_left, uniformMean_const), ActualFiniteBinarySurjectionCounting.matrix_surjective_iff_rows_independent, GrassmannCounting.card_frame and frameProduct, and ActualFiniteFrameProductDuality.frameProduct_ratio_duality / frameProduct_ratio_eq_product. The FullRowFrame bridge follows the pinned source's surjectiveMatrixFrameEquiv pattern and Matrix.toLin'_apply' equivalence.

## Remaining verification

No source theorem in this offer is claimed compiled, axiom-profiled, or reviewed. The parent still needs to compile the exact source and dependency capture in GCP, resolve diagnostics, inspect all requested axiom reports, obtain immutable capture acknowledgement, and request independent review. The finite exact-rational model reported by the parent is corroborating finite-case evidence only and does not replace those steps or establish the theorem for all dimensions.


## Full112 repair delta and exact compiler findings addressed

This offer starts from the immutable Full111 captured input `full111-phi-repair-capture-v2/ExactPhiEigenrelation-v4.lean` (SHA-256 `4AFB8BB4E49FFABF67783DDCEB83859C73280828FDC3060B8ABFC0D20BD0A75B`). The complete parent diagnostic is `stage-4.stdout` in `C:\a8gcp\498f7ba6.tar.gz` (archive SHA-256 `29A942FBF1594E1C09EC34ECE58DB02F1742E8B9FDCDA0E88B3084E3F4B7F192`).

The repair delta is limited to: (1) unfold `dotProduct` in both directions of `matrix_rows_kernel_iff`, so the matrix-entry sum and row dot product normalize to the same expression; (2) construct a named `hEmpty : IsEmpty ...` proof and use `Fintype.card_eq_zero_iff.mpr hEmpty`, avoiding a local instance-style declaration flagged by the style linter; and (3) remove the trailing `ring` after `field_simp`, since the captured compiler reports that `field_simp` already closes the goal. Public theorem statements and imports are preserved. The Checks retain all three public `#check` and fully qualified `#print axioms` requests.

This is only a source repair offer. It has not been compiled, kernel-checked, or axiom-profiled. No acceptance or certification claim is made.
