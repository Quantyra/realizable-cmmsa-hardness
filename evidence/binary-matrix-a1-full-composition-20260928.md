# Full manuscript A1 hybrid derivative composition

`BinaryMatrixA1Composition.manuscript_A1_restrict_filter` proves manuscript (A1) on the actual finite binary carriers, for every `n,d`, `A₂≤A₁≤V`, `B₁≤B₂≤W`, arbitrary ambient base `T:V→W`, arbitrary next base `S:V/A₂→B₂`, every real-valued source function `f`, and every point of the nested quotient/subtype carrier. The output is identified with `Hom(V/A₁,B₁)` through `nestedCarrierEquiv`.

The ambient hybrid filter retains exactly frequencies `Y:W→V` with `A≤im Y` and `Y⁻¹(A)≤B`; the typed carrier hybrid filter uses the same conditions on `Hom(B₂,V/A₂)`. `initialDerivative_eq_restrict_hybridFilter` and `nextDerivative_eq_restrict_hybridFilter` identify the spectral candidates with affine restriction after these actual filters. The proof transfers first-stage Fourier coefficients with an explicit collision sum, collapses the second filtered frequency sum, applies both directions of `selected_nested_iff`, and uses the exact arbitrary-base affine law and cyclic trace phase. No independence or noncollision assumption is introduced.

The result includes zero dimensions and order-zero cases. It certifies the exact A1 composition identity only; A22, positive-rank hypercontractivity, fourth-moment induction, MZ NO decoder, and the numerical NO-soundness gap remain open. The numeric gap is unchanged by this identity alone.
