# Typed Fourier on the actual A1 carrier

`BinaryMatrixA1TypedFourier` proves finite trace-character Fourier orthogonality and inversion on the actual quotient carrier `Hom(V/A,B)` and its frequency dual `Hom(B,V/A)` for every `n,d,A,B`, including zero-dimensional carriers. The uniform means divide by the exact finite cardinality of their respective carrier; `carrier_dual_card` proves these cardinalities equal using finite-basis matrix transpose. The pairing is nondegenerate in both directions, with rank-one witnesses, so finite character sums cancel without a positivity assumption on dimensions.

`carrierFourier_inversion` reconstructs every real-valued function on `Hom(V/A,B)` from its coefficients normalized by the carrier cardinality. This directly supplies the Fourier uniqueness needed when the first A1 affine restriction coalesces frequencies and the second hybrid filter acts on the resulting function.

The full manuscript A1 derivative composition still requires the canonical double-quotient/subtype carrier equivalence and a function-level composition theorem connecting the two filters and arbitrary bases `T,S`. This theorem does not reduce the numerical NO-soundness gap.
