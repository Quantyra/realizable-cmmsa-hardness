# Exact append operator continuation: argument and API map

Status: source-shaped target contracts only; uncompiled and unproved. No
material acceptance or certification is claimed. This candidate keeps the
original contract: arbitrary real `F`, the actual append with unrestricted
`B`, paired inverse basis action, independent full-row-rank `C`, and every
degenerate carrier. It does not replace a missing theorem with a conditional
oracle.

## Complete mathematical argument

Let `d = c+s`. On `Mat(n,d)`, let `F` be invariant under every paired inverse
right action: `F(MU)=F(M)` whenever `UV=VU=1`. Let

`T F(M) = E_{B in Mat(n,s)} F([M B])`,

where `B` ranges over all matrices, including zero and dependent ones. Let
`G H(W) = E_R H(WR)`, where `R : Mat(d,c)` ranges uniformly over all
full-column-rank matrices. Let
`Phi F(W) = E_{B,C} F(W+BC)`, independently, where `B : Mat(n,s)` is
unrestricted and `C : Mat(s,d)` ranges uniformly over full-row-rank matrices.
These are the manuscript operators and use their own exact finite-carrier
normalizations.

For `G(TF)=Phi F`, average first over a uniform invertible `d`-by-`d`
matrix `U=[R S]`. Every fixed full-column-rank `R` has exactly
`prod_{j=c}^{d-1}(2^d-2^j)` completions `S`: append the columns successively,
excluding the span of the previous columns. The number is positive and
independent of `R`, so the first `c` columns have the uniform full-column-rank
law. Write the bottom `s` rows of `U^{-1}` as `C`. Inversion is a bijection of
the invertible matrices. Every full-row-rank `C` has the same positive number
of top-row completions, hence this inverse block is uniform on all such `C`.
This also covers `c=0`, `s=0`, and `d=0`: the empty frame has one choice and
the zero-dimensional invertible matrix carrier contains its identity.

For fixed `U=[R S]` and unrestricted `B`, the paired-inverse action gives
`F([M R\ B] U^{-1})=F([M R\ B])`. From `UU^{-1}=I`, if the top `c` rows of
`U^{-1}` are `A` and bottom `s` rows are `C`, then `RA+SC=I`. Block
multiplication therefore identifies
`[M R\ B]U^{-1}=MRA+BC=M+(B-MS)C`. For each fixed `U`, translation
`B -> B-MS` is a bijection of the entire `Mat(n,s)` carrier. Thus the
translated `B` remains uniform and independent of `U`, hence independent of
its block `C`. Averaging proves the exact `G(TF)=Phi F` law without making
`B` full-rank or conditioning the append.

For a character `chi_Y`, the unrestricted `B` average in `Phi` vanishes unless
`YC^T=0`. This is equivalent to every row of `C` lying in `ker(Y)`. If
`rank(Y)=i`, that kernel has dimension `d-i`; the number of full-row frames
inside it is the ordered-frame count `frameProduct (d-i) s`, while the total
number is `frameProduct d s`. If `s>d-i`, the numerator count is genuinely
zero; this is the eigenvalue's zero factor. In all cases `Phi chi_Y=lambda_i
chi_Y`, with

`lambda_i = prod_{j=0}^{s-1} (2^(d-i)-2^j)/(2^d-2^j)`.

Finite Fourier reconstruction then gives `Phi(P_i F)=lambda_i P_i F` for any
real `F`; invariance is needed to ensure `P_i F` has the same paired-inverse
invariance, supplied by the existing rank-projection covariance theorem.

For the restricted adjoint identity, let `K` be invariant on `Mat(n,d)` and
`H` arbitrary on `Mat(n,c)`. The product carrier bijection `(M,B) <-> [M B]`
gives
`<T K,H>_c = <K, H(first c columns)>_d`. Average the latter integrand over
the paired-inverse action on the full carrier. Invariance of `K` preserves the
inner product, and the first-`c`-column marginal of uniform `GL(d,2)` is the
uniform full-column-rank `R` law proved above. The result is the exact
restricted adjoint ` <T K,H>_c = <K,G H>_d`. No unrestricted adjoint claim is
used. Combining this identity with the `Phi` eigenrelation and Fourier rank
orthogonality recovers the exact real same-function cross-level identity;
the independently qualified cross-level source already proves that final
identity by another route.

## Actual source/API map

The exact bytes inspected were the qualified Full109 records (source names
below are the preserved module paths in those records) and the pinned
Full107 source bodies named below. The Full109 native milestone covers 348
sources, 261 profiles, and seven stages. This is API/source inspection only;
it does not confer native evidence on these new contracts.

| Required step | Existing actual API | Remaining translation |
|---|---|---|
| Actual unconditional append and carrier order | `ActualFixedFunctionalAppendOperator.appendAverage`, `appendBinaryMatrixEquiv`, `appendBinaryMatrix`; Full107 pinned source `review-sources/lean/PvNP/RealizableHardness/ActualFixedFunctionalAppendOperator.lean` | Lift the product-carrier reindex to the exact sum/card-normalized inner-product equation. |
| Appended-character action | `ActualAppendFourierCrossLevelOrthogonality.appendAverage_character`; `BinaryMatrixFourier.character_orthogonality` | These already prove the append kills a character with nonzero appended frequency; they do not give the `G`/`Phi` transport. |
| Fourier projection and invariance | `ActualFiniteAppendSpectral47.rankProjection_mul_right_eq`; `fourierCoeff_mul_right_transpose_eq`; `rankProjection_parseval_restricted_eq` in `ActualFiniteAppendSpectral47ExactInhabitant` | Use covariance to pass the exact arbitrary-`F` right-invariance premise to each rank projection. |
| Exact real energy and cross-level consequences | `ActualFiniteFrameProductDuality.append_rank_projection_energy_eq_product`; `ActualAppendFourierCrossLevelOrthogonality.uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero`; Full109 source contracts `append_rank_cross_level_gram_eq_product` | These do not prove `Phi`'s pointwise eigenrelation, the `G(TF)=Phi F` identity, or the restricted adjoint. |
| Ordered frame count | pinned `GrassmannCounting.frameProduct`, `card_frame`; Full109 `ActualFiniteBinarySurjectionCounting.card_surjective_linear_maps` and `ActualFiniteBinaryImageFibres` | Specialize the frame count to rectangular matrix subtypes and prove zero-card/positive-card facts used by exact normalized sums. |
| Full-rank block marginals | No matching declaration occurs in the inspected Full109 operator sources | Prove both directions of the completion-count equivalence for `[R S]` and `[A; C]`; prove the completion counts are constant and positive, including zero-width cases. |
| Phi character eigenrelation | `appendAverage_character` and ordered-frame count are relevant inputs | Translate `YC^T=0` iff the row frame lies in `ker(Y)`, count the kernel frames with exact zero cases, then extend from characters by finite Fourier reconstruction. |

## Precise blocker and next path

The mathematical argument is complete, and the listed source APIs support its
operator-level ingredients. A faithful theorem body is not ready in this
candidate because the qualified source set contains no `G`, `Phi`, full-rank
completion-marginal, or restricted-adjoint implementation to reuse, and the
current records do not pin/inspect the required rectangular-frame equivalence
and completion-count bodies. Authoring those theorem bodies without first
settling the exact full-rank subtype/count APIs would risk an unverified
normalization or rank-guard change. The accompanying Lean file therefore
defines the exact operators and records the four full target propositions; it
does not assert them as theorems.

Next coherent increment: inspect and pin the complete current source bodies
for the rectangular independent-frame count and finite GL APIs; implement the
two completion-count equivalences with explicit `c=0`, `s=0`, and `d=0`
cases; then prove `G(TF)=Phi F` and the restricted adjoint over exact
sum/card means. Reuse `appendAverage_character` for Phi's character action,
prove the kernel-frame count/eigenrelation, and lift by Fourier inversion.
Carry the original paired-inverse invariant real `F` through the target
statement. Run none of those theorem compilations locally; offer immutable
successor bytes to the sole GCP compiler and capture their exact hashes. No
GCP, compiler, Git, network, or provider-review action was performed here.

Remaining to-do list: inspect/pin GL and rectangular-frame APIs; prove both
completion marginals and zero cases; translate the four exact operator goals;
then compile on GCP and obtain required source trace and independent reviews.
