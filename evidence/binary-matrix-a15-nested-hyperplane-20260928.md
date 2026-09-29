# A15 nested hyperplane carrier handoff

`hyperplaneCanonicalEquiv` identifies `Hom(V/A,H)` with
`Hom(V/A,B₁)` for `H ≤ B` and `B₁ = H.map B.subtype`. The fixed-base
law identifies `B.subtype ∘ (S + H.subtype ∘ N)` with
`B.subtype ∘ S + B₁.subtype ∘ hyperplaneCanonicalEquiv(N)` for every
base `S` and displacement `N`.

The induced actual affine restriction preserves every fibre bijectively,
restriction order, and normalized complex norm-square energy. The reverse
restriction map yields a full up-to-order globalness equivalence.
`canonical_hyperplane_oneStep_A15_global` consumes that equivalence and
the typed hyperplane one-step theorem: for every fixed base and complex
input, globalness through order `k+1` yields globalness through order `k`
on the canonical next carrier at exactly `4 * 2^(4*(k+1)) * ε`.

This closes the canonical hyperplane carrier handoff needed for A15
iteration. Rank-projection and selected-derivative intertwining across
successive canonical carriers, the accumulated A15 product, and the
original verifier-to-MZ decoder handoff remain open. The numeric
NO-soundness gap is unchanged.
