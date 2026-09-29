# Full typed arbitrary-line A15 one-step globalness

For every `A ≤ V`, `B ≤ W`, one-dimensional `L ≤ V/A`, fixed base
`T : Hom(V/A,B)`, complex function `f`, rank parameter `k`, and
`ε ≥ 0`, `typed_line_oneStep_A15_global` proves:

If `f` is up-to-`k+1` `ε`-global on **all actual affine restrictions**
of `Hom(V/A,B)`, then the actual typed reduced-carrier witness
`N ↦ P_k f(T+N∘q_L)` is up-to-`k`
`4 · 2^(4(k+1)) · ε`-global on **all actual affine restrictions** of
`Hom((V/A)/L,B)`. The base `T` remains arbitrary and fixed.

The proof identifies the reduced carrier with its adapted coordinate
matrix space by an exact affine bijection. It proves fibre image,
order, and normalized complex norm-square energy preservation in both
directions, including every base, zero order, and degenerate dimension.
The coordinate complex A15 bound is then transported through the
fixed-base affine offset; translations preserve the full globalness
quantifier. The factor has no extra transport loss.

This closes the domain-line one-step globalness portion of manuscript
A15 on the typed A1 carrier. Codomain-hyperplane transport, the rank
level identity A14 on typed carriers, peeling arbitrary hybrid
constraints through complex A1, and the final influence bound remain
open. The numeric NO-soundness gap is unchanged.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobalChecks`
passed (2297 jobs). The reduced globalness equivalence and typed
one-step theorem depend only on `[propext, Classical.choice, Quot.sound]`.
