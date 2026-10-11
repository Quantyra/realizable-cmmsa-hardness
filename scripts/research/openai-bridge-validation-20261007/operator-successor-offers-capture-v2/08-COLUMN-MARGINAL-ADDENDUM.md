# Addendum: full-column prefix marginal

The source candidate now includes both directions of the transpose rank
bridge. `transpose_of_injective_is_surjective` uses Mathlib's
`Matrix.mulVec_injective_iff`, `row_transpose`, and the project theorem
`ActualFiniteBinarySurjectionCounting.matrix_surjective_iff_rows_independent`.
The converse proves independent rows yield injective columns by
`Matrix.col_transpose` and the same APIs. `rowColumnFrameEquiv` packages the
two directions. The finite paired-inverse carrier has an involutive
`inversePairTranspose`, which reverses the inverse equalities correctly.

`columnPrefixMap` sends a paired inverse matrix to the full-column frame
obtained by transposing the first-row frame of the transposed matrix.
`column_prefix_uniform_mean` transports the row-prefix mean through those two
equivalences. `inversePairEquivGL` identifies the paired-matrix carrier with
Mathlib's actual `Matrix.GeneralLinearGroup` units, and
`gl_column_prefix_uniform_mean` states the result directly over that GL
carrier. Its codomain is every full-column frame, with its own uniform
normalizer, and it has no positive-dimension guard. No numerical fibre count
is introduced.

Pinned APIs read in the local Full107 review bodies:

| API body | SHA-256 | Declarations |
|---|---|---|
| `ActualFiniteBinarySurjectionCounting.lean` | `BA136FC5CA364B14F76447954F47EDE670930B042F1EA8276A11675B50C76C2F` | `matrix_surjective_iff_rows_independent` |
| Mathlib `LinearAlgebra/Matrix/ToLin.lean` | `9AEFBF5B4504A069DD6AD05D5A1C8E5A0D7BA9CA5FF9317F360B25CEE806B1CD` | `Matrix.toLin'_apply'`, `Matrix.mulVec_injective_iff` |
| Mathlib `LinearAlgebra/Matrix/Defs.lean` | `42CF62056A34210624ACADEEC32077EB22259619303CABC6678887B51262D6E3` | `row_transpose`, `col_transpose`, transpose involution |
| Full109-pinned Mathlib `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` | `6DDE3FF0AAA8741E68A89B589751B107771156281B67AE67847103589E2C7C61` | `Matrix.GeneralLinearGroup` is the matrix-units carrier, with stored two-sided inverse |

The candidate has not been run through Lean and is not a verified or accepted
proof. It also does not yet instantiate the GL-column mean into the project
operator module's named `FullColumnFrame` Fintype presentation. Still absent
is the bottom-s row marginal used by the restricted-adjoint argument: it
should use the selector `Fin.natAdd c : Fin s → Fin (c+s)` directly, not a
forced `c+s ↔ s+c` reindex. Generalizing the row-selector API to an arbitrary
injective `e : Fin k → Fin d` will yield that step and keeps c=0/s=0 direct.

The exact project operator mapping remains: `appendAverage` and
`appendBinaryMatrixEquiv` from Full107 `ActualFixedFunctionalAppendOperator`,
`appendAverage_character` from Full107 `0604-ActualAppendFourierCrossLevelOrthogonality`,
and the Full109 product energy formula in `ActualFiniteFrameProductDuality`.
The present candidate does not yet compose those APIs into G(TF)=Phi with
unrestricted B, prove the restricted adjoint with invariant K and arbitrary H,
or author the arbitrary-real-F Phi eigenrelation. Root's cross-level identity
trace/review and subsequent GCP/provider work remain pending. No local
Lean/Lake/elan, Git, GCP, network, or provider action was run.

Remaining to-do list: instantiate this mean on the actual operator frame
carrier; generalize to the bottom-s row selector and prove that marginal;
complete G/Phi, arbitrary-F eigenrelation, and restricted-adjoint proofs; run
the requested independent checks and review.
