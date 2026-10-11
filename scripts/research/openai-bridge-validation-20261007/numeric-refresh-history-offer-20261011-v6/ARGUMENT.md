# Actual numeric refresh count offer v6

This is a disjoint source successor to the frozen v5 capture. It offers source-level Gaussian, actual Zoom, actual dependent Candidate, and all-candidate fresh-failure mass bounds. It is not a Lean acceptance or manuscript refresh.

## Mathematical route

For `b <= N`, the pinned ratio identity gives

`gaussian N b = 2^(b*(N-b)) * normalizedFrame N b / normalizedFrame b b`.

The frame ratio is at least one because normalized frames are monotone in the ambient dimension. For the upper estimate, `normalizedFrame N b <= 1`, while the self-frame is at least `1/4`: at positive `b`, split off the last factor `1/2` and use the half bound for the preceding product; `b=0` is immediate. Thus the exact coarse bounds are `2^(b*(N-b)) <= gaussian N b <= 4*2^(b*(N-b))`.

`GrassmannFlagPosterior.card_relativeUpper` identifies the actual subtype of d-subspaces containing Q with the Grassmann count in `W/Q`. Hence `|Zoom(Q,P)| = gaussian(finrank(W)-a,d-a)`. With ambient dimension n, `a + codim(W) <= r`, `r <= d`, and `r+d <= n`, the exponent is at least `(d-r)*(n-r-d)`; therefore each actual candidate zoom has at least `2^((d-r)*(n-r-d))` elements.

The count source encodes an actual candidate `(a,Q,P)` into its actual finite stratum `(a,c,W,Q,g)`, where `c=codim(W)`, keeping the subtype `Q <= W` and the actual functional `g : W*`. It proves injectivity and counts by strata with `a+c<=r`. The W stratum embeds by the actual dual annihilator into `Grass(V*,c)`, so it has at most `gaussian(n,c)` choices. The advice subtype is bounded by all `gaussian(n,a)` advice spaces, and `|W*|=2^(n-c)`. The two Gaussian upper bounds and `a+c<=r` give at most `16*2^(n*(r+1))` elements per stratum; fewer than `(r+1)^2` budget pairs give

`Fintype.card (Candidate V d r) <= 16*(r+1)^2*2^(n*(r+1))`.

Let `p=2^-d` and `L=2^((d-r)*(n-r-d))`. For each candidate, the small-intersection branch has empty failure event. In the other branch the distinct actual coordinate count Z satisfies `p*|Zoom| <= |Z|`; the actual strict-tail mass is at most `exp(-p*|Z|/3) <= exp(-p^2*L/3)`. The union proof sums the actual event masses using `eventMass_candidateFailureSet_le`, then applies the candidate cardinality bound. It does not infer a mass bound from an upper bound on each event's exponential proxy. The resulting bound is

`16*(r+1)^2*2^(n*(r+1))*exp(-2^((d-r)*(n-r-d)-2*d)/3)`.

The final expression is the source-level `p^2*L` form in the theorem.

## Source/API corrections in v6

The Gaussian source imports and opens the true owners: `ActualBinaryGrassmannSamplingBounds` for `normalizedFrame_mono`, `GaussianRatio` for the ratio/frame lemmas, and the numeric formal/tail offers for `matchCount`, `RefreshTable`, and `matchTailEvent`. The count source directly imports/opens `ActualFiniteLaw`, `NumericRefreshFormalOffer`, and `NumericRefreshTailOffer` for its law and event declarations.

The pinned full107 source review confirms `Subspace.dualAnnihilator_inj`, `Subspace.dual_finrank_eq`, and `Submodule.finrank_le`. The last is used to establish the ambient upper bound required when turning codimension equations into exact dimensions. The advice dimension in `candidate_zoom_card_lower` is the Nat `c.1.val`, not the subtype proof `Q.property`; `candidateZoom_card_eq_actual` uses named implicit parameters. The frame quarter proof uses zero/successor cases, and the exponent comparison rewrites the second-factor upper bound in the needed direction.