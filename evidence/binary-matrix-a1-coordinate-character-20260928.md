# A1 coordinate character bridge

`BinaryMatrixA1CharacterBridge.tracePair_matrix` identifies the typed cyclic trace pairing of the transposed frequency map `Yᵀ:𝔽₂^n→𝔽₂^d` with the existing entrywise `BinaryMatrixFourier.pairing Y M`, for every `n,d,Y,M`. `traceCharacter_eq_matrix_character` then identifies the typed trace character with the existing matrix Fourier character. The proof uses the standard coordinate basis, matrix multiplication, and exchange of finite sums; it includes zero dimensions.

Together with `BinaryMatrixA1Phase.traceCharacter_carrier_base`, this closes the ambient coordinate-character bridge used by the affine phase in manuscript A1. The nested carrier identification and full function-level A1 composition remain open. Typed Fourier orthogonality/inversion was added separately in `BinaryMatrixA1TypedFourier`. This result does not change the numeric NO-soundness gap.
