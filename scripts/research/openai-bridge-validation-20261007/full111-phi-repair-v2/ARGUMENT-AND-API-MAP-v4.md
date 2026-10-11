# Exact Phi eigenrelation candidate v4

Status: uncompiled author continuation. This is a source offer with concrete Lean proof bodies, not kernel-verified evidence. The parent compiler owner has not run this candidate through the pinned GCP compiler. The accompanying ExactPhiEigenrelationChecks-v4.lean requests the three public signatures and #print axioms reports.

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
