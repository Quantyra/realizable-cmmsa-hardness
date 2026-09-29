# A1 coordinate character bridge

`BinaryMatrixA1CharacterBridge.tracePair_matrix` identifies the typed cyclic trace pairing of the transposed frequency map `Yᵀ:𝔽₂^n→𝔽₂^d` with the existing entrywise `BinaryMatrixFourier.pairing Y M`, for every `n,d,Y,M`. `traceCharacter_eq_matrix_character` then identifies the typed trace character with the existing matrix Fourier character. The proof uses the standard coordinate basis, matrix multiplication, and exchange of finite sums; it includes zero dimensions.

Together with `BinaryMatrixA1Phase.traceCharacter_carrier_base`, this closes the character-definition bridge for the affine phase in manuscript A1. Typed Fourier orthogonality/inversion on `Hom(V/A,B)`, the nested carrier identification, and full function-level A1 composition remain open. This result does not change the numeric NO-soundness gap.
