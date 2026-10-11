# Addendum: full normalized row-prefix marginal

The current source now also contains `rowPrefixMap`,
`rowPrefixMap_surjective`, `rowPrefixFiberEquiv`, and
`row_prefix_uniform_mean`. The domain is the finite subtype of paired square
matrices U,V with both `U*V=1` and `V*U=1`. The codomain is the subtype of all
full-row-rank c-by-(c+s) binary matrices. The map sends `(U,V)` to `P*U` for
the canonical first-c-coordinate selector P.

The proof establishes surjectivity by the square completion theorem. It
transfers each generic function-fibre to the matrix-equality fibre, uses the
explicit right-transporter equivalence for every pair of full-row frames,
and obtains one positive common fibre cardinal from surjectivity. The
existing sigma-fibre sum theorem then proves equality of normalized uniform
means. Thus the complete first-row marginal has a candidate proof without a
numerical fibre count. All zero cases use the same definitions and arguments.

This does not yet establish the analogous bottom-s-row marginal needed in the
restricted-adjoint route. The API can be generalized from `Fin.castAdd s` to
an arbitrary injective row selector `e : Fin k → Fin d`; in particular,
`Fin.natAdd c : Fin s → Fin (c+s)` selects the last s rows directly. That
generalization is still to author. The full-column frame-to-transposed-row
surjectivity bridge also remains open, as do the original operator
connections: exact G(TF)=Phi with unrestricted B and invariant F, arbitrary-F
pointwise Phi eigenrelation, and the restricted adjoint for invariant K and
arbitrary H. Root continues the trace/recovery work; this candidate was not
compiled or accepted. No local Lean/Lake/elan, Git, GCP, network, or provider
action was run.

Remaining to-do list: generalize row selection and prove the bottom-row
marginal; prove the full-column transpose/rank bridge; connect both marginals
to the actual append/operator APIs; complete and review G/Phi/eigenrelation/
restricted-adjoint.
