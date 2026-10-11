# Selected-coordinate robust refresh and distinct-advice bound

## Scope and status

This offer assembles the manuscript-selected numeric parameters with the
actual finite-cover and distinct-advice theorems. It is an uncompiled Lean
translation candidate. The core theorem returns the strong local bound
`D/(8*m*2^(4h^2)) < sum`, where `D` is the actual original ordinary-star
density. It supplies neither an inverse witness nor a preserving refresh as
a premise. The frozen dependencies remain unchanged.

## Exact argument

Fix the original selected instance `(L,m,A)`, put `h = hBlock L m`,
`t = leafT m h`, `s = leafK m h`, `d = t+s`, and
`r = numericRankThreshold m`. Keep the input center and ordinary leaf tables
at the exact dimensions consumed by the fixed-coordinate inverse. The pinned
`selected_numeric_height` theorem gives `256 ≤ m`, `r ≤ h`, and
`numericBase base m ≤ h`; since the numeric base is the maximum of the
user-supplied base and `numericHnum m`, this yields
`numericHnum m ≤ h`. The pinned selected spectral theorem, on the same
selector equality and the same `hBlock L m`, gives `t+s=2h`, positive leaf
tail, and the exact selected `rho=1/bOf m`. No height or cutoff is increased.

Let `e = refreshThreshold m h`, preserving the exact real threshold used by
the inverse. `refresh_threshold_bounds` gives
`2/(2^(2h)) ≤ e/2`, hence the cover's required noise inequality after using
`d=t+s=2h`; it also gives `0<e`. The coordinate ambient is
`CoordAmbient (blocks A h)`, whose finrank is `2*blocks A h`. From
`1≤A`, `h² < blocks A h`, and `h≤h²`, we obtain `2h≤finrank`; together
with `r≤h`, all cover dimension guards hold.

For the fixed finite set `X` equal to the union of every original-good
candidate zoom at threshold `e`, `numeric_actual_failure_mass_lt_one` applies
at dimension `2h`, using the actual candidate count and actual sum of
failure-event masses. Thus a concrete fresh table preserving every candidate
exists. For each such table `T'` whose ordinary-star density is at least half
the original density, the input lower bound `2*S≤StarDensity(T)` implies
`S≤StarDensity(T')`, where `S` is the exact rational success margin at
`badExponent m h`. Call
`fixed_coordinate_real_inverse_agreement` with the original `(L,m,A)`, the
original selector, center law, and this arbitrary `T'`. Its selected-height
and spectral derivations are internal. The resulting witness has the same
rank `r`, exact budget `q+codim(P.W)=r`, nonempty zoom, and strict agreement
above `Real.rpow 2 (-2*(1-1000*rho^2)*h)`. The selected identity
`rho=1/bOf m` identifies this threshold with `e` exactly. This constructs the
universal `hinverse` required by the finite-cover theorem, without assuming it.
The inverse theorem returns its whole existential with dimension `d=t+s`,
while the cover requires dimension `2h`. The translation explicitly transports
`T'` from `2h` to `d` with `Eq.mpr` and simplifies the complete inverse
existential along `d=2h`. This moves the dependent `DecodedPair` together with
its budget equality, Zoom cardinality, and agreement statement against `T'`.

Apply `good_cover_mass_lower_bound` to this concrete `hinverse`, the concrete
bad-mass result, the actual ordinary-star tables, and `X`. Then apply
`summed_good_advice_fraction_density_lower` to the resulting strict cover
mass inequality. This gives `D/(8*m*2^(4h^2)) < sum` directly. From
`2*S≤D` it implies `S/(4*m*2^(4h^2)) < sum`; from `4*S≤D` it implies
`S/(2*m*2^(4h^2)) < sum`. The advice index remains `a : Fin(r+1)` and its
threshold remains the same `e`; no distinct-Q count or conditional
probability is introduced at this composition boundary.

## Dependency boundaries

- `ExactCoordinateNumericInverse.fixed_coordinate_real_inverse_agreement`
  is used for every table in the half-density range; it is not a hypothesis.
- `ActualRefreshNumericPreservation.numeric_actual_failure_mass_lt_one`
  supplies the actual bad-event bound for the whole fixed cover; it is not a
  hypothesis.
- `ActualRefreshGoodCover.good_cover_mass_lower_bound` supplies the cover
  density from that inverse and bad-mass proof.
- `ActualDistinctAdviceAverage.summed_good_advice_fraction_density_lower`
  supplies the Gaussian distinct-advice aggregation.
- All frozen sources retain their existing bytes and capture identities.

## Checks / limitations

No Lean/Lake compiler or GCP execution was available to the author. The
translation is not accepted or compiled. The dependent dimension transports
from `t+s` to `2h` are explicitly written with the selected equality and need
native validation by compiler custody. No axioms or terminal compiler result
are claimed here.
