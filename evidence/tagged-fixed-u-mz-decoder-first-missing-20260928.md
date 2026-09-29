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
