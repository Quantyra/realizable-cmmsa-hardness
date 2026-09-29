# Matrix-lift homogeneous comparison: intersecting anchor

## Scope and manuscript link

This increment proves the homogeneous-experiment comparison in the proof of
`paper/body.tex` Lemma `matrix-lift` (the paragraph beginning “For the homogeneous
experiment”). It covers any finite binary vector space `V`, any independent fixed
anchor frame `f : Frame V a` with span `Q`, any sampled subspace `H`, and any
intersection `Q ⊓ H` of dimension `z`. The internal frame `s : Frame V z` is an
explicit basis witness for that intersection. No disjointness, positivity of `k`,
or nonempty zoom assumption is used in the fibre or sum identities.

For every eligible `L : Grass V (a+k)` with `Q ≤ L ≤ Q ⊔ H`, the Lean theorem
`card_homFibre_GL` counts actual ordered free-column tuples `B : Fin k → H`
with `[f,B]` full rank and image `L`:

`card (HomFibre f H L) = 2^(z*k) * Nat.card (GL (Fin k) (ZMod 2))`.

The count follows from an explicit equivalence with the existing anchored
`SpanFibre` inside `L ⊓ H`. Theorems
`independent_concatenate_iff_intersection`,
`span_concatenate_iff_intersection`, and `finrank_lift_inf` prove that this
internalization preserves rank and the exact image. In particular,
`finrank (L ⊓ H) = z+k` even when `Q` intersects `H`.

`sum_hom_rankArrays` disintegrates every full-rank homogeneous tuple by its
actual image `L`. `homLiftTest` assigns zero to each deficient tuple.
`homogeneous_lift_density_le` then proves, for every `e ≥ 0` and arbitrary
real table `g`, that the zoom sum bound

`∑ eligible L, g(L) ≤ e * card(eligible L)`

implies the unconditioned homogeneous bound

`∑ B : Fin k → H, homLiftTest f H g B ≤ e * card(Fin k → H)`.

This is the exact homogeneous comparison used before the manuscript's
full-row-rank affine-target loss. It does **not** prove the affine-target
comparison, exact-budget zoom refinement, entire matrix-lift lemma, fixed-`U`
MZ decoder, or final NO-soundness exponent. It reduces the Lean gap by closing
the arbitrary-intersection homogeneous count and density step; the numerical
NO bound remains unproved.

## Verification

`lake build PvNP.RealizableHardness.MatrixGrassmannIntersectingAnchorChecks`
completed successfully: 2,468 jobs. Its `#print axioms` output for the rank and
span bridges, exact fibre count, GL-factor identity, sum disintegration, and
homogeneous density theorem contained only `[propext, Classical.choice,
Quot.sound]`. The Checks file instantiates `k=0` and `z=0`. The increment has
no `sorry`, `admit`, or custom axiom.
