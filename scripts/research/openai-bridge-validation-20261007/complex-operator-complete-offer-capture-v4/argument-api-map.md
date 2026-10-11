# Complex append continuation v4: argument and API map

Status: authored candidate; not compiled, certified, accepted, or independently reviewed. The interrupted v1 bytes and immutable v2 offer remain preserved in their original directories and are not edited here. This v4 source and its operator-law extension are the sole current offer. No claim is made that its Lean elaboration succeeds.

## Main theorem and exact route

`complexAppend_rankProjection_energy_eq_product` states the exact `normSq` energy equality for the literal unconditional complex append average. It assumes only `i ≤ c+s` and paired-inverse right invariance of arbitrary complex `F`. It does not assume full rank of the appended block, nonzero values of `F`, or nonempty dimensions. The scalar is the original product over `Fin s`, with no factor of two.

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
- `complexPhi_rankProjection_eigen`: optional pointwise eigenrelation for arbitrary complex `F`, derived by the real/imaginary components from `phiAverage_rankProjection_eigen`. Its dependency is the frozen uncompiled real v4 candidate. It assumes `s ≤ d`, the nonempty full-row-frame guard.

## Pinned source dependencies

- `BinaryMatrixFourier.lean`, Full107 qualified source record, SHA-256 `810324DDAD55B909A4EBA239FA3CB6988858A9426DC77ADEBEC051B0C11A70D8`.
- `ActualFixedFunctionalAppendOperator.lean`, Full107 qualified source record, SHA-256 `EB71A55A38E8922333058F0D05D8E48472003AAA9BEE2B9F01A9DE00668A7B77`.
- `ActualFiniteFrameProductDuality.lean`, Full107 qualified source record, SHA-256 `39E80A821DE4B51E8AC2A74CF9A0967D7CD3EA45D730E7DD47C0B2C144245DCE`; exports the real product-energy equality used by the main theorem.
- `ExactAppendOperatorContracts.lean`, immutable real operator definitions at `exact-operator-continuation-candidate-v3/`.
- `ExactPhiEigenrelation-v4.lean`, `exact-phi-eigenrelation-candidate-v1/`, SHA-256 `B1177090ABB0AFA8E09CD9505DD3AC78C9445656C8B20F4C86D66AF325B9CCEE`; uncompiled and used only by the optional Phi eigenrelation.
- Pinned Mathlib imports: `Mathlib.Basic.Complex.Basic`, `Mathlib.Basic.Complex.BigOperators`, `Mathlib.Algebra.BigOperators.Field`, and `Mathlib.Tactic`. In particular, the explicit `Complex.BigOperators` import supplies real/imaginary finite-sum transport.

## Scope and remaining obligations

The complex two-function sesquilinear Gram law and whole hypercontractivity appendix remain outside this offer. The pointwise Phi eigenrelation does not substitute for the two-function law. All imported real candidates and these complex candidates require exact GCP compilation, diagnostics, axiom/profile checks, dependency/source hash capture, native custody, and independent review by the authorized root workflow. The static preflight is lexical only and does not establish parsing, elaboration, kernel checking, or theorem acceptance.

## Complex operator continuation added in v4

`ExactComplexOperatorLaws.lean` adds the next complete operator milestone:

- `complexGAverage` is the literal normalized finite complex mean over every `FullColumnFrame`, with exact real/imaginary transport to the existing `gAverage`. The generic carrier mean remains total, including the empty-carrier case; no denominator cancellation is used.
- `complexG_append_eq_phi` proves the exact literal complex `G(TF)=Phi(F)` equality for arbitrary paired-inverse right-invariant complex `F`. It transports invariance to both real components and invokes the real finite-frame identity separately. Append remains over every unrestricted B; Phi samples the product of unrestricted B and full-row C.
- `complexInnerProduct` uses the conjugate-first convention `E(conj(K) * H)`. Its real and imaginary formulas are stated and proved exactly, retaining the imaginary sign.
- `complexRestrictedAdjoint_exact` proves the restricted adjoint for the complex pairing. Only the full-space first argument K is invariant; base-space H is arbitrary. The proof applies the real restricted adjoint to four component pairs and splits the real finite mean over sums. It makes no unrestricted-adjoint claim.

The v3 scalar-left Phi eigenrelation is repaired in v4 with the zero-factor simp rules required by `Complex.mul_re` and `Complex.mul_im`. This does not change the theorem statement.

## Frozen real theorem dependencies for the v4 operator extension

These files are exact source pins from `exact-operator-continuation-candidate-v3/`. They remain explicitly uncompiled; the complex offers do not certify them.

- `ExactAppendBlockIdentity.lean`, SHA-256 `97076955CDB280238F18E511C1E66E5B64E1541E9CFE080561C98686CEFFC689`; the extension calls `ExactAppendBlockIdentity.g_append_eq_phi`.
- `ExactRestrictedAdjoint.lean`, SHA-256 `1BF81FA70064A4657FEBB0E82CC2C17C6901280BC24F1EB0CE0AFE7558137864`; the extension calls `ExactRestrictedAdjoint.restricted_adjoint_exact`.
- `ExactAppendOperatorContracts.lean`, SHA-256 `4F288DE5D06D01A188391431F9096ED87FDB273209670F4479F8FAC497F4860C`; supplies real frame and operator definitions.
- `ExactPhiEigenrelation-v4.lean`, SHA-256 `B1177090ABB0AFA8E09CD9505DD3AC78C9445656C8B20F4C86D66AF325B9CCEE`; remains an uncompiled dependency of the pointwise Phi eigenrelation.

`ExactComplexAppendContinuationChecks.lean` and `ExactComplexOperatorLawsChecks.lean` include fully qualified `#print axioms` requests for the public theorem offers so the full-scope harness can collect them independently of namespace-open commands.

The complex two-function rank-Gram law and whole hypercontractivity appendix remain outside this offer. No real two-function Gram sequel is imported or assumed. All v4 Lean sources remain uncompiled, uncertified, unaccepted, and without independent review.
