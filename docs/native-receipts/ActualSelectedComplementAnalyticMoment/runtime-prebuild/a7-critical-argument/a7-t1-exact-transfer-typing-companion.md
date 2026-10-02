# T1 notation and typing companion

This companion supplements the captured `a7-t1-exact-transfer-derivation.md` (SHA-256 `727D08D5069F751A85887E735672BA0FC8DF6E3969DF72A605F509283EB951F1`). It does not edit or replace that preserved artifact. It records two precision fixes requested in Root's mathematical review. This is still argument-only material; it is not a Lean implementation or full A7 claim.

## Correctly typed triple-to-map bijection

Fix `A <= V` and `B <= W`, and write `q_(C in A): A -> A/C` and `q_B: W -> W/B`. For a T1 index triple,

```
C <= A,  H >= B,  Xbar : H/B ~= A/C,
```

the map counted by the `2^(i*j)` argument has codomain `W/B`, not `H/B`. It is

```
theta = j_(H/B -> W/B) o Xbar^(-1) o q_(C in A) : A -> W/B,
```

where `j_(H/B -> W/B)` is induced by the inclusion `H <= W`. Then
`ker(theta)=C` as a submodule of `A`, and `im(theta)=H/B` as a subspace of
`W/B`.

Conversely, start with any linear map `theta:A -> W/B`. Its kernel is first
formed inside `A`; the corresponding subspace of `V` is

```
C = (ker(theta)).map A.subtype <= V.
```

Let

```
H = q_B^(-1)(im(theta)) <= W.
```

Then `B <= H`, and the restriction of `q_B` induces an isomorphism
`H/B ~= im(theta)`. The first isomorphism theorem for `theta` gives
`A/C ~= im(theta)`. Composing these induced isomorphisms gives
`theta_bar:A/C ~= H/B`; set `Xbar=theta_bar^(-1)`. By construction the two
directions recover the same kernel, image, quotient map, and inverse
isomorphism, so they are literal inverses. For `theta=0`, `C=A`, `H=B`, and
both quotient spaces are zero. For `dim(A)=0` or `dim(W/B)=0`, there is
exactly one map and exactly the corresponding unique triple. Thus the count
is exactly `|Hom(A,W/B)|=2^(dim(A)*codim(B))`, including all zero cases.

## Forward rank decomposition with realized summands

For an ordinary-selected `Y`, put `C=Y(B) intersect A` and
`H=B+Y^(-1)(A)`, and let

```
R = q_C o Y|H : H -> V/C,
Xtilde(b+z)=Yz+C, for b in B and z in Y^(-1)(A).
```

Every `h in H` has such a representation, and

```
R(b+z) = (Yz+C) + (Yb+C).
```

The first summand lies in `A/C`; as `z` ranges over `Y^(-1)(A)`, it realizes
all of `A/C`, because `A <= im(Y)`. The second lies in `Y(B)/C`; as `b`
ranges over `B`, it realizes all of `Y(B)/C`. Conversely every value of
`R` is a sum of these two kinds of values by the displayed decomposition of
`h`. Therefore

```
im(R) = (A/C) + (Y(B)/C).
```

Their intersection is zero: an element common to both lifts to
`A intersect Y(B)=C`, hence is zero modulo `C`. Thus this is the direct sum
decomposition

```
im(R) = (A/C) direct_sum (Y(B)/C),
```

with `im(Xtilde)=A/C` and `im(R-Xtilde)=Y(B)/C`. This proves rank
additivity by both image containment and independent realization; disjointness
alone is not being used to assert that `im(R)` has the full stated range.

## Review boundary

These typing clarifications strengthen the explicit inverse/count and
rank-additivity presentation of T1. The parent derivation's reverse
selector, uniqueness, physical-carrier transport, phase, and output-frequency
arguments remain as written. The complete A7 proof still requires its later
T2, degree, graph-count, W6 aggregation, and final summation steps, and is not
claimed here. No source or compiler action is authorized by this note.
