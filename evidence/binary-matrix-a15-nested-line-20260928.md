# A15 nested line carrier handoff

The `lineCanonicalEquiv` maps the reduced carrier
`Hom((V/A₂)/(A₁/A₂),B)` to `Hom(V/A₁,B)` using the canonical quotient
equivalence, for every `A₂ ≤ A₁`. Its actual affine restriction map
preserves each fibre bijectively, the restriction order, and normalized
complex norm-square energy. The converse restriction map proves a full
up-to-order globalness equivalence.

`canonical_line_oneStep_A15_global` consumes this transport and the
typed line A15 theorem. For any rank-one `A₁/A₂`, fixed base
`T : V/A₂ →ₗ B`, complex input, and all actual restrictions, it sends
globalness through `k+1` to globalness through `k` on the canonical next
carrier at exactly `4 * 2^(4*(k+1)) * ε`. This is the line handoff for
iterated A15 peeling.

The corresponding hyperplane canonical handoff and rank-projection/
derivative intertwining under canonical reindexing remain open. The full
product `2^(4kℓ−2k²+4k) ε` is not yet proved; numeric MZ NO-soundness
remains unchanged.
