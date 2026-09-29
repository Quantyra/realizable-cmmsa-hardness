# Actual affine row-target matrix lift

The file `lean/PvNP/RealizableHardness/MatrixLiftAffineTarget.lean` proves the
factor-two comparison on the manuscript's ordered free columns, after the
normal form `M = [V,N]`, with homogeneous row kernel `H` and a surjective
residual row map `X₁ : H →ₗ[ZMod 2] C`.

For every fixed full-rank target `B : Fin k → C`, every nonnegative
rank-image score `g`, and every nonnegative eligible zoom density bound `e`,
`affine_target_zoom_density_le_two_e` bounds the normalized score on the
actual fibre `rowTarget H X₁ N = B` by `2*e`. Its finite counting premise is
`card(all targets) < 2*card(full-rank targets)`. For binary
`C = Fin c → ZMod 2`, `c < k`, this is now discharged by
`MatrixFullRowRankHalf.full_row_rank_gt_half` in the separate concrete
bridge.

The proof establishes equal cardinality of every affine target fibre,
transitivity of full-rank targets under a right `GL(k)` coordinate change,
preservation of the actual `extensionTest` rank and image score, equal score
sum on full-rank target fibres, exact denominator factorization, and a
fibrewise score sum. The homogeneous score is definitionally the same
`homLiftTest` used by `MatrixGrassmannIntersectingAnchor.homogeneous_lift_density_le`.
No rank conditioning replaces the zero-on-deficiency experiment.

This is the affine-target part of manuscript Lemma `matrix-lift`. The normal
form reduction from arbitrary nominal constraints, exact-budget zoom
refinement, and the final fixed-`U` robust decoder remain separate Lean
obligations. Thus this result advances the matrix-lift route to the decoder;
it does not close the numerical NO-soundness gap.

Verification: targeted `lake build
PvNP.RealizableHardness.MatrixLiftAffineTargetChecks` passed 2,469 jobs.
`#print axioms` for the equal-fibre, orbit, full-rank score equality,
normalized factor-two, and zoom-density comparison reports only
`[propext, Classical.choice, Quot.sound]`. The integrated bridge Checks
passed 2,471 jobs with the same standard-axiom boundary.

## Three-lens review

| Lens | Verdict | Evidence and limit |
|------|---------|--------------------|
| Build/audit | GO | Independent `lake build PvNP.RealizableHardness.MatrixLiftAffineTargetChecks`: 2,469 jobs, standard axioms only. |
| Proof-adversarial | GO-WITH-NOTES | Actual ordered-column fibres, score invariance under right GL action, equal denominators, and zero deficient score are proved. `hhalf` and surjective residual map are explicit. |
| Complexity | GO-WITH-NOTES | Matches the normalized affine-target step. The direct count is now proved separately; nominal-constraint normal form and exact-budget zoom refinement remain. |
| Non-claims | GO | Evidence confines the result to the conditional factor-two step; full matrix-lift, decoder, and numeric NO remain open. |
