# Addendum: concrete rectangular completion

Historical source-step note. Its final “Remaining to-do list” predates the
operator source additions. See `OPERATOR-COMPOSITION-IMPLEMENTATION-ADDENDUM.md`
for the current candidate map; all current Lean source remains uncompiled.

This addendum supersedes the earlier v2 map's statement that the rectangular
completion theorem is still missing. The existing map remains unchanged as an
original offer. The new source file is still an uncompiled candidate.

`RectangularGLRowCompletion.exists_square_completion` states that for every
surjective linear map represented by a binary matrix `M : BinaryMatrix c
(c+s)`, there are square matrices `U,V` satisfying `U*V=1`, `V*U=1`, and
`P*U=M`, where P is the canonical prefix matrix. P is the matrix of
`LinearMap.funLeft (Fin.castAdd s)`. Its surjectivity follows from
`LinearMap.funLeft_surjective_of_injective`; this covers c=0 and s=0 without
separate branches. Both M and P have range top, so the exact Full107 project
API `same_range_matrix_right_orbit` applies directly.

Pinned source APIs read for this step:

| Source body | SHA-256 | Declarations used |
|---|---|---|
| Full107 `BinaryMatrixRightOrbit.lean` | `409FD652E1F051E92688466EAC57BD6B85AF93866D5F5D4C9AA0152AB25286B0` | `same_range_matrix_right_orbit`: paired inverse matrices and `N * U = M` |
| Full107 `BinaryMatrixSameRangeOrbit.lean` | `8864F1152CF47819087237E2151134EBE4766ED06AA0603E44A9DCE095A73EE7` | same-range surjective-map equivalence underlying the matrix theorem |
| Full107 Mathlib `Algebra/Module/Equiv/Basic.lean` | `5AAC385B195A2A8AAFFB2B483E619403CB87017AE602C46A8ED6A3C5391DC67F` | `LinearMap.funLeft`, `funLeft_surjective_of_injective` |
| Full107 Mathlib `LinearAlgebra/Matrix/ToLin.lean` | `9AEFBF5B4504A069DD6AD05D5A1C8E5A0D7BA9CA5FF9317F360B25CEE806B1CD` | `Matrix.toLin'_toMatrix'`, matrix/linear-map correspondence |
| Full107 Mathlib `LinearAlgebra/Matrix/Rank.lean` | `4CE457849B67ECA2D37842F1EBCAC1DEA88F16A202F5C6DFCEB4BB6C6047E262` | `rank_transpose`, `rank_eq_finrank_range_toLin` |

The completion is directly useful for the row-prefix map `U -> P*U`. For any
two full-row frames X,Y, the right-orbit theorem supplies an invertible
transporter T with `X*T=Y`. Right multiplication `W -> W*T` maps the fibre
over X to the fibre over Y; its inverse is multiplication by T's paired
inverse. The remaining Lean work is to package that map as an equivalence of
finite fibre subtypes, and to bridge full column independence to surjectivity
of the transposed matrix. The inspected Mathlib rank declarations and the
Full107 `MatrixFullRowRankHalf` source show the intended rank/finrank/range-top
route, but this candidate has not yet written that exact bridge theorem.

The finite sigma-fibre sum and normalized-mean theorem in
`RectangularFrameFiberAverage.lean` consume those equivalences. The current
generic lemma still has an explicit positive common fibre-size parameter; the
actual GL fibre equivalence must also establish nonemptiness (or the direct
surjectivity of the prefix map) to discharge positivity. No numerical fibre
count is needed.

Actual operator APIs mapped in the original argument remain `appendAverage`
and `appendBinaryMatrixEquiv` from the Full107 body of
`ActualFixedFunctionalAppendOperator.lean`, and `appendAverage_character` from
`0604-ActualAppendFourierCrossLevelOrthogonality.lean`. Neither actual API is
yet connected to this rectangular completion. G/Phi, arbitrary-real-F Phi
eigenrelation, and restricted-adjoint obligations remain unproved. Root's
cross-level identity trace/review and all GCP/provider work remain outside
this candidate. No Lean/Lake/elan, Git, GCP, network, or provider command was
run.

Remaining to-do list: prove full-column transpose/rank bridge and finite
prefix-fibre equivalences with c=0 and s=0; connect this marginal to actual
append/operator APIs; then complete and review the G/Phi/eigenrelation/
restricted-adjoint argument.
