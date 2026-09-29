# Ordinary-star weighted functional selection review

Satellite commit `7293d45` proves a bounded all-ambient selection step for
arbitrary **fixed predraw** center and leaf tables `C,T`. With
`t <= d <= finrank V`, `1 <= d-t`, nonempty center and leaf fibres, and
`m(d-t)+E+2 <= finrank V-t`, an ordinary-star acceptance density of at least
`successMargin E` has jointly direct accepting mass greater than half that
margin. Every such star has exactly `M = 2^(finrank V-(t+m(d-t)))` matching
global functionals; each center label has exactly
`B = 2^(finrank V-t)` matching functionals, among
`F = 2^(finrank V)` total.

The weighted first-moment argument selects a single functional `f` with
matching-star mass `X` and matching-center mass `beta` satisfying
`(successMargin E/4)*(M/B)*beta + (successMargin E/4)*(M/F) <= X <= beta`.
These are the exact ratio coefficients in the proved statement. Under the
dimension guard they correspond to the manuscript's
`2^(-m(d-t))` and `2^(-(t+m(d-t)))`, but that power rewrite and the ensuing
numeric lower bound on `beta` are not yet proved in this increment. The
fixed-table good-star count uses joint directness, which is needed to glue
the center and leaf labels on their full span.

| Review lens | Bounded selection | Tagged transport, inverse, robust `8S`, core Theorem 1 |
| --- | --- | --- |
| Proof adversarial | GO-WITH-NOTES | INCOMPLETE |
| Complexity theory | GO-WITH-NOTES | INCOMPLETE |
| Non-claims boundary | GO-WITH-NOTES | INCOMPLETE |

The tagged complement law is proved separately. Its transport into this
ordinary-star selection statement, the Fourier/all-ambient inverse bound,
and the changed-ambient `8S` application remain open. This increment does
not reduce the numerical NO-soundness gap.
