# Exact-budget zoom refinement for matrix lift

## Force theorem

`lean/PvNP/RealizableHardness/MatrixLiftExactBudgetZoom.lean` proves the
fixed-upper-space incidence comparison used at the end of the proof of
`paper/body.tex` Lemma `matrix-lift`. For every finite binary ambient `V`,
every `Q : Grass V q`, `W : Grass V w`, `r < d`, `e ≥ 0`, and real table
`g : Grass V d → ℝ`, `ExactBudgetZoomBound r d g e` says that **every
nonempty** zoom with lower dimension plus upper codimension exactly `r`
has density at most `e`. If the actual zoom budget
`q + (finrank V - w)` is at most `r`, `smaller_budget_of_exact_r` proves
the same density bound on `Between Q W d`. Empty original or refined
intervals are covered; no conditional law is assigned to an empty zoom.

The proof sets the intermediate dimension to
`a = r - (finrank V - w)`, so `q ≤ a ≤ d` follows from the actual budget
and `r < d`. `betweenInsideEquiv` and `card_between` give the exact
constant count of extensions inside `W`. `refineFlagEquiv` double-counts
flags `Q ≤ Q' ≤ L ≤ W`; each `L` has the same number of intermediate
`Q'`, and each `Q'` has the same number of containing `L`. A positive
Gaussian count permits cancellation without assuming that the original
zoom is nonempty.

`homogeneous_lift_density_of_exact_r` identifies this interval with
the exact `HomEligible f H k` zoom for `W = Q ⊔ H` and invokes
`MatrixGrassmannIntersectingAnchor.homogeneous_lift_density_le`.
Consequently, the manuscript's global exact-budget premise supplies the
unconditioned homogeneous matrix-lift density bound, including zero
contribution from rank-deficient free-column tuples. The intersection
`Q ⊓ H` remains arbitrary.

This closes the exact-budget refinement and homogeneous comparison steps
inside the matrix-lift proof. The full nominal affine restriction reduction,
fixed-`U` MZ decoder, and final numerical NO-soundness inequality remain
unproved. It reduces the matrix-lift part of that gap; the final NO
exponent is unchanged.

## Verification

Local `lake env lean` of both the source and Checks file exited 0. On the
authenticated GCP builder, an isolated `/tmp/cmmsa-exact-budget-20260929`
checkout was populated from local `git archive fbd374c`, with SHA-256
matches for `lakefile.toml` and the prior homogeneous source. The two new
files were copied separately and their local/remote SHA-256 hashes matched:

- `MatrixLiftExactBudgetZoom.lean`:
  `4193fabce59c8f0d2bcb2c807d90d31b1a8f8bb20ab65adb7abe4fc7874cdd32`
- `MatrixLiftExactBudgetZoomChecks.lean`:
  `c47926f813b31e76d0fe1361a568b508a92ffef8188b3d9ba996acba53788e7e`

The isolated GCP target build
`lake build PvNP.RealizableHardness.MatrixLiftExactBudgetZoomChecks`
completed successfully (2,469 jobs). Its `#print axioms` results for all
nine force theorems listed only `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, or custom axiom occurs in this increment.

The builder could not fetch GitHub over port 443, so the base tree was
streamed from the local pushed commit and the missing `cslib` package was
linked from an existing checkout at the matching `d9be641` commit. The
dirty canonical builder checkout was not edited. The local full Checks
artifact build had stopped at its final write while C: was full; the GCP
build supplied the completed target verification.
