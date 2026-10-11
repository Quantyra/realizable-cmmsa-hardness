# Exact real two-function rank-Gram candidate

Status: uncompiled source candidate. It is not accepted proof evidence and does not certify the uncompiled operator dependencies it imports.

## Exact statement

Let `d=c+s`, let `F,H : BinaryMatrix n d → Real` both satisfy the original paired-inverse right-invariance predicate on the entire `n × d` matrix carrier, and let `P_i` be the original rank-`i` Fourier projection. The candidate proves, for all natural ranks `i,j` without an `i≤d` or `j≤d` premise,

`E_M[(T(P_i F))(M) (T(P_j H))(M)] = λ_j E_W[(P_i F)(W) (P_j H)(W)]`,

where `T` is the actual append average over every `n × s` matrix and `λ_j = ∏_{k<s} ((2^(d-j)-2^k)/(2^d-2^k))`, with natural subtraction in the numerator exactly as in the candidate Phi eigenrelation. The theorem `append_rank_two_function_gram_cases` combines this with the exact Fourier slice law: the Gram entry is zero when `i≠j`; when `i=j`, it is `λ_i ∑_{rank Y=i} fhat(Y) hhat(Y)`. This equal-rank expression is bilinear and has no same-function substitution.

The operator identity itself has no rank guard. If a rank exceeds `d`, the corresponding Fourier filter is empty and the projection is zero. Thus the operator identity still applies; the cross-rank and equal-rank consequences retain this zero-projection behavior, including `s=0` where the finite product is the empty product `1`.

## Proof map

1. `rankProjection_rightInvariant` wraps the exact qualified declaration `ActualFiniteAppendSpectral47.rankProjection_mul_right_eq`. That declaration performs the transposed paired-inverse reindex of the Fourier-frequency sum, applies the captured right-action Fourier covariance to the coefficient, and preserves rank under the invertible action. It requires no rank fit condition.
2. `rankProjection_eq_zero_of_width_lt_rank` discharges the above-width edge case directly from the actual matrix bound `Matrix.rank_le_width`; the filtered rank-projection carrier is empty when `d<i`.
3. `fourier_inner_mean_eq_sum` expands one arbitrary real function by the actual finite `fourier_inversion` theorem and exchanges finite sums. It gives `E[FH]=∑_Y fhat(Y) hhat(Y)` directly; it is not obtained by polarization from a same-function square identity.
4. The captured `fourierCoeff_rankProjection` theorem identifies the coefficient support of `P_i F` as exactly `rank Y=i`. Applying the direct bilinear identity to `P_i F,P_j H` gives the common-slice formula. Disjoint slices yield `rankProjection_cross_rank_inner_eq_zero` for two arbitrary real functions.
5. For the operator Gram identity, instantiate the exact restricted adjoint with invariant first argument `K=P_i F` and arbitrary second argument `Hbase=T(P_j H)`. Projection invariance discharges only K's invariance condition. Since `P_j H` is invariant, `g_append_eq_phi` rewrites `G(T(P_j H))` as `Phi(P_j H)`. The arbitrary-real-input eigenrelation `phiAverage_rankProjection_eigen` then contributes `λ_j P_j H`; pull out the scalar from the normalized finite mean.
6. Substitute the common-slice formula to produce the exact cross-rank zero and equal-rank bilinear theorem.

## Actual source/API dependencies

| Source/API | Use in the candidate | Evidence identity/status |
|---|---|---|
| Full109 `ActualFiniteAppendSpectral47.rankProjection_mul_right_eq` | Exact right invariance of every rank projection under the original paired-inverse action | Frozen source declaration in the Full109 archive; Full107 review source SHA-256 `371FD673C07AC5DDDD6EE66B62D50EFDD0E1A7F6C27AABB7212779CE948F25CC`. Its qualified native status is inherited evidence, not a fresh compile here. |
| Full109 `BinaryMatrixRightFourierCovariance.fourierCoeff_mul_right_of_basis_invariant`, `character_mul_right`, `rightBasisEquiv` | Captured all-matrix right-action Fourier covariance used by the projection-invariance body | Qualified source file SHA-256 `CF8990EAA1D049716774E3C31B8939C27015F64036226EA758F3A1BCA28C9E4B`. |
| Full109 `BinaryMatrixFourier.fourier_inversion`, `fourierCoeff_rankProjection`, `character_orthogonality` | Direct bilinear Parseval and disjoint rank-support Fourier calculation | The original finite Fourier API is part of the immutable Full109 archive (SHA-256 `F5C8D78779B0ABE00A21DE9C960719B0BC6CE6978AA97382F699F0EC519593EC`). No operator Gram identity is imported from the same-function cross-level theorem. |
| Full107 `BinaryMatrixFourier` | Exact source body for real characters, normalized mean, Fourier inversion, rank projections, coefficient support, and character orthogonality | Review source SHA-256 `810324DDAD55B909A4EBA239FA3CB6988858A9426DC77ADEBEC051B0C11A70D8`. |
| Full107 `ActualFixedFunctionalAppendOperator`, `ActualFiniteFrameProductDuality` | Original unconditional append and actual frame/product definitions inherited by the operator contracts | Review source SHA-256 values `EB71A55A38E8922333058F0D05D8E48472003AAA9BEE2B9F01A9DE00668A7B77` and `39E80A821DE4B51E8AC2A74CF9A0967D7CD3EA45D730E7DD47C0B2C144245DCE`. |
| V3 `ExactAppendOperatorContracts` | Exact `RightInvariant`, `gAverage`, `phiAverage`, and actual append definitions | Uncompiled candidate SHA-256 `4F288DE5D06D01A188391431F9096ED87FDB273209670F4479F8FAC497F4860C`; captured within the operator-complete v3 offer. |
| V3 `ExactRestrictedAdjoint.restricted_adjoint_exact` | Restricted adjoint with only the first full-carrier argument invariant | Uncompiled candidate SHA-256 `1BF81FA70064A4657FEBB0E82CC2C17C6901280BC24F1EB0CE0AFE7558137864`; captured within the operator-complete v3 offer. |
| V3 `ExactAppendBlockIdentity.g_append_eq_phi` | Actual G-after-unrestricted-append equals independent B/full-row-frame Phi for invariant inputs | Uncompiled candidate SHA-256 `97076955CDB280238F18E511C1E66E5B64E1541E9CFE080561C98686CEFFC689`; captured within the operator-complete v3 offer. |
| Phi v4 `ExactPhiEigenrelation.phiAverage_rankProjection_eigen` | Pointwise eigenrelation for arbitrary real input and every rank, including empty projections | Candidate SHA-256 `B1177090ABB0AFA8E09CD9505DD3AC78C9445656C8B20F4C86D66AF325B9CCEE`; uncompiled. |

The v3/v4 source references above are exact offered dependencies, not certified dependencies. The new statements in this directory also require a native full-scope compile, fresh public `#print axioms` output, exact source/dependency capture, GCP proof closure, and independent review before any proof-acceptance claim.

## Public candidate declarations

- `rankProjection_rightInvariant`: arbitrary `F` satisfying the original right-invariance predicate; no rank guard.
- `rankProjection_eq_zero_of_width_lt_rank`: exact empty-projection case for `d<i`.
- `fourier_inner_mean_eq_sum`: arbitrary real `F,H`.
- `rankProjection_inner_mean_eq_frequency_sum`, `rankProjection_cross_rank_inner_eq_zero`, `rankProjection_equal_rank_inner_eq_frequency_sum`: arbitrary real `F,H`; distinct-rank zero and exact equal-rank slice.
- `append_rank_two_function_gram`: arbitrary invariant real `F,H`, all natural ranks, exact λ-scaled Gram identity.
- `append_rank_two_function_gram_eq_zero`, `append_rank_two_function_gram_eq_lambda`, `append_rank_two_function_gram_cases`: the two exact cases and their combined if-statement.

`ExactRealRankGramChecks.lean` checks each public declaration and requests fresh axiom reports. Those Checks have not been run.

Remaining to-do list: root native elaboration of the candidate and every imported offered dependency; fresh axiom/GCP and source-capture diagnostics; independent review. No new real operator dependencies are certified by this offer.
