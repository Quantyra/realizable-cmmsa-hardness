# Complex append continuation v2: argument and API map

Status: authored candidate; not compiled, certified, accepted, or independently reviewed. The v1 bytes remain preserved in `exact-complex-append-candidate-v1/` and are not edited here. This v2 source is the sole successor offer. No claim is made that its Lean elaboration succeeds.

## Main theorem and exact route

`complexAppend_rankProjection_energy_eq_product` states the exact `normSq` energy equality for the literal unconditional complex append average. It assumes only `i ? c+s` and paired-inverse right invariance of arbitrary complex `F`. It does not assume full rank of the appended block, nonzero values of `F`, or nonempty dimensions. The scalar is the original product over `Fin s`, with no factor of two.

The proof transports paired-inverse invariance to `re F` and `im F`, applies the pinned Full107 real theorem `append_rank_projection_energy_eq_product` to each component, and adds the two equalities. `Complex.normSq_apply` plus a pointwise ring identity gives the component energy split. Literal complex append and rank projections are transported pointwise to their corresponding real operations, so the resulting theorem is about the original unconditional append carrier and its own normalized mean.

## Source/API map

- `complexFiniteMean`: literal finite complex sum divided by the complex cast of the finite carrier cardinality. Its re/im lemmas use pinned `Complex.div_ofReal_re/im` and `Complex.re_sum/im_sum`. It is total when the carrier is empty; no denominator cancellation is used.
- `complexFourierCoeff`: literal normalized complex Fourier sum with the real binary character cast into `Complex`. The re/im lemmas identify it with `fourierCoeff` of the corresponding real component.
- `complexRankProjection`: literal finite rank-filtered Fourier sum. Its re/im lemmas identify it with the existing real `rankProjection` componentwise.
- `complexAppendAverage`: literal normalized average over every `BinaryMatrix n s`, applying `appendBinaryMatrix M B`; it is the actual unconditional append. Re/im lemmas identify it with real `appendAverage` on components.
- `complexRightInvariant_iff_components`: exact paired-inverse invariant equivalence in both directions. It uses extensionality for complex values and imposes no rank restriction on the matrix being acted on.
- `uniformMean_normSq_components`: exact decomposition of complex squared magnitude into the sum of the two real component means.
- `complexAppend_rankProjection_energy_eq_product`: main exact normSq product-energy equality, using the qualified real Full107 result.
- `complexPhiAverage`: literal mean over the product carrier of unrestricted `B : BinaryMatrix n s` and `C : FullRowFrame s d`, retaining independent uniform sampling. Its component lemmas identify it with real `phiAverage`.
- `complexPhi_rankProjection_eigen`: optional pointwise eigenrelation for arbitrary complex `F`, derived by the real/imaginary components from `phiAverage_rankProjection_eigen`. Its dependency is the frozen uncompiled real v4 candidate. It assumes `s ? d`, the nonempty full-row-frame guard.

## Pinned source dependencies

- `BinaryMatrixFourier.lean`, Full107 qualified source record, SHA-256 `810324DDAD55B909A4EBA239FA3CB6988858A9426DC77ADEBEC051B0C11A70D8`.
- `ActualFixedFunctionalAppendOperator.lean`, Full107 qualified source record, SHA-256 `EB71A55A38E8922333058F0D05D8E48472003AAA9BEE2B9F01A9DE00668A7B77`.
- `ActualFiniteFrameProductDuality.lean`, Full107 qualified source record, SHA-256 `39E80A821DE4B51E8AC2A74CF9A0967D7CD3EA45D730E7DD47C0B2C144245DCE`; exports the real product-energy equality used by the main theorem.
- `ExactAppendOperatorContracts.lean`, immutable real operator definitions at `exact-operator-continuation-candidate-v3/`.
- `ExactPhiEigenrelation-v4.lean`, `exact-phi-eigenrelation-candidate-v1/`, SHA-256 `B1177090ABB0AFA8E09CD9505DD3AC78C9445656C8B20F4C86D66AF325B9CCEE`; uncompiled and used only by the optional Phi eigenrelation.
- Pinned Mathlib imports: `Mathlib.Basic.Complex.Basic`, `Mathlib.Basic.Complex.BigOperators`, `Mathlib.Algebra.BigOperators.Field`, and `Mathlib.Tactic`. In particular, the explicit `Complex.BigOperators` import supplies real/imaginary finite-sum transport.

## Scope and remaining obligations

This candidate does not formalize complex `G(TF)=Phi(F)`, the restricted complex adjoint, the two-function sesquilinear Gram law, or the whole hypercontractivity appendix. The optional Phi eigenrelation is not a substitute for those interfaces. All imported real candidates and this candidate require exact GCP compilation, diagnostics, axiom/profile checks, dependency/source hash capture, native custody, and independent review by the authorized root workflow. The static preflight is lexical only and does not establish parsing, elaboration, kernel checking, or theorem acceptance.
