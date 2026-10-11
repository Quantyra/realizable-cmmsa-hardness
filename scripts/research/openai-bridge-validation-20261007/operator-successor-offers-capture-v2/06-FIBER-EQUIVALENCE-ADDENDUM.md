# Addendum: explicit equipotent row-prefix fibres

This intermediate addendum is superseded by `ROW-MARGINAL-ADDENDUM.md` and
`COLUMN-MARGINAL-ADDENDUM.md`, which record the subsequent marginal and
transpose candidate theorems. `RectangularGLRowCompletion.prefix_fiber_equiv` states an
equivalence between the fibres over any two surjective rectangular row
matrices. It obtains T,S from the pinned Full107 orbit theorem with `X*T=Y`,
`T*S=1`, and `S*T=1`, and maps an inverse pair `(A,B)` to `(A*T,S*B)`. Its
inverse maps `(C,D)` to `(C*S,T*D)`. The prefix condition follows from
`P*(A*T)=(P*A)*T`; the two subtype inverse laws reduce to the two paired
matrix identities. This retains every direction explicitly and introduces
no product-cardinality premise. The same-range theorem gives the transporter
for all full-row frames, including the zero-dimensional cases.

Together with `exists_square_completion`, this supplies actual rectangular
row completion and equal fibre sizes for the row-prefix map. The generic
finite sigma-fibre argument then gives its normalized marginal, assuming the
prefix codomain is represented by the full-row subtype and the Fintype
instances are exposed. The present candidate has not yet instantiated that
row-frame codomain directly in `uniformMean_map_of_equipotent_fibers` at that
intermediate stage. Actual `appendAverage` /
`appendBinaryMatrixEquiv`, G/Phi, arbitrary-real-F Phi eigenrelation, and the
restricted adjoint are still not connected or proved here. No Lean/Lake/elan,
Git, GCP, network, or provider action was run.

Remaining to-do list: instantiate finite row-frame fibre means, prove the
full-column transpose/rank bridge, connect to the actual append/operator APIs,
and complete/review G/Phi/eigenrelation/restricted-adjoint.
