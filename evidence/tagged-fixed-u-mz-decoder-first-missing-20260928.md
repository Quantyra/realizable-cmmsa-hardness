# First missing theorem after the tagged fixed-U density bound

`ActualTaggedMZSideDraw.composedLegalValue_gt_forces_side_threshold_U`
already supplies fixed center and full-domain leaf tables and mass at least
`8·2^-p` of eligible first questions `U` whose exact side-conditioned
test density is at least `8·2^-p`. Here `p` encodes
`S = 2^{-2(1-1000ρ)hm}`. The tables are fixed before the conditional
center and leaf draws. The theorem does not return a decoder.

The first missing pointwise theorem is the robust enlarged-ambient local
decoder for **each fixed good U and these fixed tables**. Under the
manuscript's admissible parameters `m≥2`, `0<ρ≤1/4000`, integral
`r=10m/ρ`, `t=2(1-ρ)h`, leaf dimension `d=2h`, sufficiently large `h`,
`J=2^(2^(Ah²))` with `A` fixed before `h`, ambient dimension `3J`, and
equation-space dimension `J`, it must take the actual transverse
side-conditioned density `≥8S` and return integers `a,c` with
`a+c≤r` such that at least `2^-6h²` of **uniform** `a`-subspaces `Q`
admit a codimension-`c` subspace `W⊇Q+H_U` and a linear `g` on `W`
respecting `H_U`, with agreement at least
`2^{-2(1-1000ρ²)h}/5` on the conditioned transverse Grassmann space.
The pair `a,c` must be fixed before the successful `Q` draw.

No theorem with this conclusion is present in the tagged Lean modules.
The manuscript proves it as Lemma `robust-local` from its explicit
inverse-agreement Lemma `inverse-explicit`, exact complement identity,
refreshing argument, and fixed-pair counting. Those decoder ingredients
have no corresponding tagged Lean import. The scoped MZ Theorem 4.2
contract at input density `S` is also explicitly external in the
manuscript; it does not by itself formalize the changed-ambient `8S`
application. The outer NO contradiction additionally needs the cited
maximal-pair/outer hardness machinery after this decoder output.

This audit changes no numerical NO-soundness bound. The existing
fixed-table class-collision charge and the `8S` density threshold are
already upstream of this missing decoder theorem.

## Earliest missing theorem inside the manuscript proof

Following the proof of `inverse-explicit` in `paper/body.tex`, its first
unavailable Lean input is the full `matrix-lift` lemma. For every binary
ambient `E=F₂^n`, `D=F₂^d` with `n≥d` and `0≤r<d`, every `e≥0`, and every
Boolean table `g` on `Grass(E,d)` whose density is at most `e` in **each
nonempty** zoom `Q≤L≤W` with `dim Q+codim_E W=r`, define `G(M)` to be
`g(im M)` when `M:D→E` has rank `d`, and zero otherwise. The required
conclusion is basis invariance and
`BinaryMatrixFourier.PseudorandomExact r (2e) G`: conditional density at
most `2e` in every nonempty consistent nominal-budget-`r` fibre
`MU=V₀, XM=Y₀`, including dependent and zero equations.

Lean already defines the nominal `AffineRestriction` and
`PseudorandomExact` predicates and proves some finite frame/fibre counts.
It does not define this Grassmann zoom pseudorandom premise or prove its
transfer to all nominal matrix fibres. The manuscript reconstructs the
bridge from MZ Lemma 4.5 and MZ24 Lemmas A.17–A.18. Later, its
`inverse-explicit` proof also needs the positive-rank dyadic-`p` Boolean
matrix bound of `thm:binary-hc`, the finite spectral estimate, and the
moment/refreshing/counting argument. Current `BinaryMatrixFourier`
contains rank-zero and rank-level `L²` cases, not that positive-rank
`Lᵖ` theorem.

A Lean result parameterized by the matrix-lift or decoder claim would be
conditional only. Importing the scoped MZ local-decoder contract as an
explicit external premise could support a cited mathematical argument,
but would not certify the manuscript's changed-ambient `8S` decoder or
the NO contradiction in Lean. No axiom or conditional wrapper is added.

The existing representation already handles the nominal equation
boundary: `BinaryMatrixActualAffine.actualOfRaw_fibre` identifies each
nonempty raw fibre with an intrinsic affine coset, and
`actualOfRaw_order_le_budget` gives actual order at most its nominal
budget. The first substantive unproved comparison is therefore a
rank-lift density bound on **every actual affine coset of order at most
`r`** from the exact-budget Grassmann zoom hypothesis. The manuscript's
factor two comes from reducing affine row targets to a full-rank target
orbit and bounding its probability `π(c,k)>1/2`, with `c≤b<k`.
After that reduction, the homogeneous count needs a constant-fibre
theorem for fixed anchor `Q=span V` and sampled subspace `H₀=ker X₀`
without assuming `Q≤H₀`: for each eligible `d`-space `L` between
`Q` and `Q+H₀`, exactly `|GL(k,2)|·2^(zk)` full-rank ordered free-column
tuples yield `L`, where `k=d-dim Q` and `z=dim(Q∩H₀)`.
`MatrixGrassmannFibre.uniform_extension_law` handles anchors inside
the sampled ambient; it does not supply this intersecting-anchor case.
Finally, smaller actual budgets must be refined to exact zoom budget
`r` by constant-incidence averaging. These are missing proof steps,
not additional assumptions licensed by the current Lean theorems.
