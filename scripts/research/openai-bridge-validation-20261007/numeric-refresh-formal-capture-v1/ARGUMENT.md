# Exact finite dual-label refresh and adaptive history

Status: formalization offer for E002/S3137. `ExactRefresh.lean` fixes the finite carrier and update map, proves the two update equations, and contains uncompiled candidates for exact matching mass and the finite exponential-moment identity. No Markov, Chernoff/tail, Lean compilation, kernel acceptance, GCP run, final decoder, or many-Q theorem is claimed. The tail and adaptive argument below remain mathematical derivations pending translation.

The pinned robust enlarged-ambient statement is manuscript SHA-256 `16E77E937685F55BA96CD276BBDE4E65EF36F25C25B790E946F5E3EC9CFAA449`, line 754. Fix `m≥2`, `0<rho≤1/4000`, integral `r=10m/rho`, `d=2h`, `t=2(1-rho)h`,
`S=2^(-2(1-1000rho)hm)` and `e=2^(-2(1-1000rho^2)h)`. The ambient coordinate dimension is `n=2J`. A single complement and coordinate equivalence are fixed throughout. The center table is arbitrary and fixed; the original ordinary leaf table has one actual dual label for each distinct d-space. Intermediate refreshes operate on all current X coordinates in the fixed coordinate ambient and may produce arbitrary ordinary tables. The fixed-coordinate one-inverse interface and the initial density transport into this experiment are input interfaces; this argument does not assume source-NO, a final decoder, or the desired many-Q conclusion.

## Exact carrier and update

Fix a finite F₂-vector space V and dimension d. Define the distinct d-space index and its dual-label product by

```text
Grass_d(V) = { L ≤ V | dim(L) = d }
Label(L)  = Hom_F₂(L, F₂)
Omega     = Pi (L : Grass_d(V)), Label(L)
```

The product index is the type of distinct subspaces itself. A repeated leaf occurrence, repeated inverse visit, or second representation of the same L contributes no second coordinate. By `Module.card_eq_pow_finrank`, each fiber has q = 2^d elements. The exact fresh law is uniform on the finite product Omega. For any fixed arbitrary current table T0 and finite X subset Grass_d(V), update as

```text
refresh(T0, X, F)(L) = if L ∈ X then F(L) else T0(L)
```

`ExactRefresh.lean` encodes this carrier and update, including literal inside/outside equations. The update preserves all of T0 outside X; it does not condition fresh labels on the past, the selected inverse output, or the labels they replace.

## Exact match probabilities

Fix a linear map g : W → F₂, and a set Z subset X of distinct d-spaces lying in W. For each L in Z, the event F(L) = g restricted to L specifies exactly one of the q labels in Label(L). For every S subset Z, product counting gives

```text
Pr[for every L in S, F(L) = g|L] = q^(-|S|) = p^|S|, where p = 2^(-d).
```

Indeed, the constrained dependent-product coordinates are singletons and every other coordinate is unrestricted. The pinned `Finset.card_pi` / `Fintype.card_piFinset` formulas count these products coordinatewise; `Fintype.card_pi` counts the full carrier. Thus distinct-coordinate indicators are mutually independent, with the actual dual-label parameter p, not an ambient-functional heuristic. Since T0 is fixed and Z subset X, no value outside X enters this event.

Let Y count L in Z for which F(L) = g|L, and put M = |Z|. For each fresh full table F, let
`M_F = {L in Z | F(L) = g|L}`. The identity `2^|M_F| = |P(M_F)|` gives the exact finite-sum expansion

```text
2^Y = sum over S subset Z of indicator[for every L in S, F(L) = g|L].
```

Exactly the subsets of `M_F` contribute one. Exchange the finite sums over F and S. For each fixed S, the inner sum over F is the cardinality of the constrained product assignments, namely `q^(N-|S|)`, where `N = |Grass_d(V)|` and `q = 2^d`; the full carrier has cardinality `q^N`. Therefore the exact unnormalized sum and normalized average are

```text
sum_F 2^Y = sum_{S subset Z} q^(N-|S|) = q^N (1 + 1/q)^M,
E[2^Y] = (1 + 1/q)^M = (1+p)^M ≤ exp(p M).
```

The last inequality follows by applying `1+x ≤ exp(x)` to each of M factors (the pinned `Real.add_one_le_exp` / `Real.prod_one_add_le_exp_sum`). For M > 0, Markov's inequality on the finite average and `2^(2 p M) = exp(2 p M log 2)` yield

```text
Pr[Y > 2 p M] ≤ exp(-(2 log 2 - 1) p M) ≤ exp(-p M / 3).
```

The last step follows from pinned `Real.log_two_gt_d9` and rational arithmetic; no concentration library is required. If M = 0, Y = 0, so the strict bad event is empty. The strict event and zero case matter: no positive tail is asserted when there are no refreshed zoom coordinates.

This derives the exact numeric tail at the mathematical level. The Lean candidate now contains the native dual cardinal, full-product cardinal, constrained assignment cardinal, exact rational event-mass ratio, and bounded-history carrier cardinal. It does not yet formalize the ratio simplification to `q^(-|S|)`, the finite-sum exchange/moment equality, the real Markov step, or the conditional-history argument. None is smuggled into `ExactRefresh.lean` as an assumption.

## One-step preservation, uniformly over adaptive outputs

For a pre-refresh state (T0, X), take the entire finite candidate universe of zoom descriptions (Q, W, g) satisfying the manuscript dimension condition. It is fixed by the ambient and dimensions, independently of F. For one candidate let Z = X intersect Zoom[Q,W], and M = |Z|. If X intersect Zoom[Q,W] has relative mass below p, refreshed coordinates contribute less than p of that zoom without any probabilistic event. Otherwise `M≥p·|Zoom[Q,W]|`. The zoom contains exactly `[n-r choose d-a]_2` spaces, at least `2^((d-a)(n-r-d+a))`, which is at least `2^((d-r)(n-r-d))` under `a≤r` and `n-r-d≥0`. Thus the manuscript Gaussian estimate gives

```text
M ≥ 2^(-d) · 2^((d-r)(n-r-d)).
```

On the complement of Y > 2pM, matches from refreshed labels contribute at most 2p of the full zoom. The tail bound applies to every fixed candidate under the same pre-refresh state. A union bound over the whole candidate universe therefore controls any inverse output chosen after seeing F; no independence between the adaptive output and F is used.

For each dimension pair a+c=r, there are at most 4·2^(an) choices of Q, at most 4·2^(cn) choices of W, and at most 2^n linear maps W→F₂. There are at most (r+1)^2 dimension pairs. Hence the full candidate universe has size at most 16(r+1)^2·2^(n(r+1)). In the large-intersection case, the pinned zoom estimate gives `M≥2^(-d)·2^((d-r)(n-r-d))`; therefore `pM≥2^E/4` for the selected `d=2h` exponent `E=-4h+2+(2h-r)(n-r-2h)`, and the per-candidate tail is at most `exp(-2^E/12)`. Multiplying these two bounds gives exactly the manuscript one-step failure bound:

These Gaussian estimates follow from
`[N choose k]_2 = 2^(k(N-k)) ∏_(i=1)^k (1-2^(-(N-k+i)))/(1-2^-i)`.
Each numerator factor is at least its denominator, so the coefficient is at
least `2^(k(N-k))`. For the upper bound, the inverse denominator product is
less than 4: its first factor is 2, and the product of the remaining factors
exceeds `1-Σ_(i=2)^∞2^-i=1/2`. Thus `[N choose k]_2≤4·2^(k(N-k))`.
The number of d-spaces in the zoom is `[n-r choose d-a]_2`; dividing its lower
bound by the ambient upper bound `[n choose d]_2≤4·2^(d(n-d))` gives zoom
measure at least
`2^((d-a)(n-r-d+a))/(4·2^(d(n-d))) ≥ 2^(-rn)/4`.
The exponent difference after adding rn is `c(n-d+a)+da≥0`.
The dimension guards ensure `0≤d-a≤n-r`. Multiplying this zoom measure by
`[n choose d]_2` yields the stated lower bound for M.

```text
F_n = 16 (r+1)^2 2^(n(r+1)) exp(-2^E / 12)
E   = -4h + 2 + (2h-r)(n-r-2h).
```

On the one-step preservation event, every candidate's refreshed contribution is at most 2p = 2^(1-d). If the inverse returns current-table agreement greater than e, at least e-2p ≥ e/2 of that agreement lies outside X, where `refresh_outside` says the table is still exactly T0. The final inequality uses the selector guard `4p≤e`, equivalently `2000rho^2 h≥2`, which is implied by its height cutoff. This is the original-table progress used by the potential argument. The statement concerns leaf-table agreement and makes no claim about the fixed center table.

## Histories and bounded horizon

The next fresh product coordinate is independent of every finite prefix by direct counting: fixing any i coordinates leaves exactly `|Omega|^(B-i)` completions among `|Omega|^B` equally likely histories, so each prefix has mass `|Omega|^-i` and the next coordinate remains uniform conditionally. For a concrete bounded process, use a product of B_n copies of Omega, define the state at stage i recursively as a function only of the first i coordinates, and make terminated or aborted states absorbing. Conditional on any fixed prefix with an active state, the current T_i and X_i are fixed; the uniform one-step argument above applies with the same F_n. Summing over active prefixes shows that the probability of a bad active transition at stage i is at most F_n; a union bound over the B_n stages gives total failure probability at most B_n F_n. If this is less than one, a no-failure path exists; if it is less than one half, its probability is at least one half. Padding handles early stopping and does not assume termination in advance.

On a no-failure path, every successful inverse step adds more than e/2 original-table agreement on a zoom whose global mass is at least 2^(-rn)/4. Hence the union X grows by at least Delta = e 2^(-rn)/8 at each step. Since its mass is at most one, B_n = ceil(8 · 2^(rn)/e) + 1 steps cannot all occur. Density starts at epsilon_A and at termination is below epsilon_A/2. The accepted-star event can change only if one of its m leaf occurrences belongs to X. Double-counting incident pairs K subset L gives each occurrence a uniform marginal on all d-spaces, even with the common center and possible repeats; thus acceptance changes by at most m mu(X), and mu(X) > epsilon_A/(2m).

## Counting distinct Q values

For every successful inverse output, record its Q, the selected zoom, and its dimension pair (a,c), with a+ c=r. Retain only distinct Q values. For each retained Q, choose one successful visit witnessing it; repeated visits to the same Q, even with different selected zooms, do not create another counted space. Every L in X came from a selected zoom and therefore contains at least one retained Q. Thus X is covered by the union of all d-spaces containing one of the recorded Q values.

Let N_(a,c) be the number of distinct recorded a-spaces assigned to pair (a,c). The fraction of d-spaces containing a fixed a-space is `[n-a choose d-a]_2/[n choose d]_2`. The upper Gaussian bound on the numerator and lower bound on the denominator give at most `4·2^(-a(n-d))=2^(2-an+ad)≤2^(4h^2-an)`, since d=2h and the selected cutoffs give a≤r≤h and h≥1. A union bound over these actual distinct Q values, not visits, gives

```text
mu(X) ≤ Σ_(a,c) N_(a,c) 2^(4h^2-an).
```

Let T_a be the number of all a-spaces in the fixed coordinate ambient and set f_(a,c)=N_(a,c)/T_a. The pinned count T_a≤4·2^(an) implies

```text
Σ_(a,c) f_(a,c) ≥ mu(X) 2^(-4h^2)/4
                 > epsilon_A 2^(-4h^2)/(8m).
```

Now average over the fixed-complement experiment. If the mean initial ordinary star density is at least 8S and each density is at most one, the mass of complements with epsilon_A≥4S is at least 4S: the contribution from the other complements is at most 4S, so the good set must supply at least the remaining 4S. On every good complement, the preceding sum is at least `4S·2^(-4h^2)/(8m)`. Assign zero contribution on bad complements. Averaging therefore yields total summed fraction at least `2S^2·2^(-4h^2)/m`. There are at most (r+1)^2 dimension pairs, so one fixed pair (a,c) has averaged fraction at least

```text
2S^2·2^(-4h^2) / (m(r+1)^2),
```

and hence at least the manuscript's weaker `2S^2·2^(-4h^2)/(m(r+1)^3)` bound. This is an unconditional marginal over the fixed-complement experiment: successful complements form a subset of the experiment, and the Q-law is not conditioned on success. If a later step changes from the fixed coordinate ambient to enlarged-ambient advice, its correction factor is separate and is not included in this count. The refresh coordinates remain indexed by distinct L values; the force count remains indexed by distinct Q values, so repeated stars and repeated inverse visits never multiply either count.

## Optional source-carrier compatibility note

The selected proof route performs every intermediate refresh on the fixed coordinate ambient and applies the fixed-coordinate inverse to arbitrary ordinary tables. It does not require refreshed tables to satisfy source-row predicates, and it does not require transporting this product law back to full tagged-domain labels. At the final source witness, the captured side-extension argument uses the original row-valid canonical table and an H-extension; that operation is separate from the intermediate refresh law. The affine-fiber identification between a full-domain functional on H direct-sum R and an R-dual label is available as an optional interface check, not a premise of this route.
## Boundary

`ExactRefresh.lean` contains source-level candidates through matching-event mass and the finite moment identity; these remain uncompiled. The Real Markov/tail theorem, bounded conditional-history implementation, per-state preservation union bound, and complete adaptive recursion remain mathematical derivations awaiting Lean translation. The fixed-coordinate inverse and initial-density transport are input interfaces. The distinct-Q force derivation above follows from the refreshed potential, acceptance-change bound, Gaussian counts, and averaging; it is not assumed as a premise. No final decoder, source-NO implication, compilation, or theorem accepted by Lean is claimed.


