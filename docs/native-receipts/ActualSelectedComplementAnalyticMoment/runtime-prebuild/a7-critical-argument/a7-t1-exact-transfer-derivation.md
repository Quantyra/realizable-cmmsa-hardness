# A7 T1 exact transfer: selector bijection, count, and carrier transport

Status: new argument-only expansion of the T1 portion of the A7 audit. It supplements, and does not edit or supersede, the historical audit, its correction, or the accepted W6 bridge artifacts. It is a mathematical derivation and interface audit, not a Lean implementation or a claim that A7 is complete. Root review is still required before any T1 implementation is treated as authorized or accepted.

## Target and notation

Let `F = F_2`, let `Y : W -> V` be a linear map, and let `A <= V`, `B <= W`. The ordinary selector is

```
P_(A,B)(Y)  iff  A <= im(Y) and ker(Y) <= B.
```

The hybrid selector on a pair `(C,H)` is

```
L_(C,H)(Y)  iff  C <= im(Y) and Y^(-1)(C) <= H.
```

Write `q_C : V -> V/C`. For a candidate triple let `C <= A`, `H >= B`, and let `Xbar : H/B -> A/C` be a linear isomorphism. Its pullback map and the other map in the rank-poset condition are

```
Xtilde = (A/C -> V/C) o Xbar o (H -> H/B) : H -> V/C,
R      = q_C o Y|H                                  : H -> V/C.
```

These are different maps: `Xbar` is an isomorphism between quotient spaces, `Xtilde` is its map on `H` with kernel `B`, and `R` is induced by the original frequency. The condition `Xtilde <=_r R` means `rank(R) = rank(Xtilde) + rank(R-Xtilde)`; equivalently, `im(Xtilde) <= im(R)` and `R=Xtilde` on `R^(-1)(im(Xtilde))`.

The exact transfer to justify is, on the common physical carrier,

```
R_(A,B,T) P_(A,B) f
  = sum_(C<=A, H>=B, Xbar:H/B ~= A/C) D_Xbar D_(C,H,T) f.       (T1)
```

The finite sum has one term for each triple; for a fixed frequency `Y`, exactly one such triple is active when `Y` is ordinarily selected, and none is active otherwise. This is a pointwise finite Fourier reindexing, not an orthogonality assertion about potentially colliding output frequencies.

## Forward construction from an ordinary-selected frequency

Assume `A <= im(Y)` and `ker(Y) <= B`. Set

```
C = Y(B) intersect A,
H = B + Y^(-1)(A).
```

First define

```
Xtilde(b+z) = Y(z) + C,       b in B, z in Y^(-1)(A).
```

This is well defined. If `b+z=b'+z'`, then `z-z'=b'-b` is in `B` and both `Yz,Yz'` are in `A`; hence `Yz-Yz'` lies in `Y(B) intersect A=C`. Its kernel is exactly `B`: if `Yz in C`, choose `b' in B` with `Yb'=Yz`; then `z-b' in ker(Y) <= B`, so `b+z in B`. Conversely `Xtilde` vanishes on `B`. It is onto `A/C`: given `a in A`, choose `w` with `Yw=a` by `A <= im(Y)`; then `w in Y^(-1)(A) <= H` and `Xtilde(w)=a+C`.

Thus `Xtilde` descends to the isomorphism

```
Xbar : H/B -> A/C,       (b+z)+B |-> Yz+C.
```

The two definitions are compatible by `Xtilde = inc_(A/C) o Xbar o quotient_H`. This records explicitly that the quotient isomorphism is not `R` and is not itself the pullback map.

The hybrid selector accepts `Y`. Certainly `C <= im(Y)`. If `Yw in C`, write `Yw=Yb` with `b in B`; then `w-b in ker(Y) <= B`, so `w in B <= H`. Therefore `Y^(-1)(C) <= H`.

For the rank-poset condition, for `h=b+z` as above,

```
R(h)       = Yb + Yz + C,
Xtilde(h)  = Yz + C,
(R-Xtilde)(h) = Yb+C.
```

The images `A/C` and `Y(B)/C` in `V/C` have zero intersection, since `A intersect Y(B)=C`. Hence `im(Xtilde) <= im(R)` and the difference image is complementary to `im(Xtilde)`, giving `Xtilde <=_r R`.

## Reverse construction and uniqueness

Now suppose a triple `(C,H,Xbar)` satisfies `C <= A`, `H >= B`, `Xbar:H/B ~= A/C`, the hybrid selector for `Y`, and `Xtilde <=_r R`, with `Xtilde` defined by pullback as above.

The rank-poset condition gives `im(Xtilde) <= im(R)`. Since `im(Xtilde)=A/C`, every `a+C` for `a in A` has a representative `h in H` with `Yh+C=a+C`; the hybrid condition gives `C <= im(Y)`, so `a` is in `im(Y)`. Thus `A <= im(Y)`.

If `w in ker(Y)`, then `Yw=0 in C`; the hybrid preimage condition gives `w in H`. Now `Rw=0` lies in `im(Xtilde)`. Rank-poset agreement on `R^(-1)(im(Xtilde))` yields `Xtilde(w)=R(w)=0`, so `w in ker(Xtilde)=B`. Therefore `ker(Y) <= B`, proving the ordinary selector.

We next recover `C`. If `a=Yb` with `b in B` and `a in A`, then `Rb=a+C` lies in `im(Xtilde)`. Agreement gives `Xtilde(b)=Rb`; the left side is zero because `b in ker(Xtilde)=B`, so `a in C`. This proves `Y(B) intersect A <= C`. Conversely, for `c in C`, hybrid selection gives `w` with `Yw=c` and `w in Y^(-1)(C) <= H`. Thus `Rw=0`; zero lies in `im(Xtilde)`, so rank-poset agreement gives `Xtilde(w)=0`. Hence `w in ker(Xtilde)=B`, proving `c in Y(B)`. Together with `C <= A`, this establishes `C=Y(B) intersect A`.

With `C` known, recover `H`. If `Yw in A`, then `Yw+C` belongs to `im(Xtilde)`, hence to `im(R)`. Choose `z in H` with `Rz=Yw+C`. Then `Y(w-z) in C`; hybrid selection implies `w-z in H`, and therefore `w in H`. Thus `Y^(-1)(A) <= H`, so `B+Y^(-1)(A) <= H`.

For the reverse inclusion, take any `h in H`. Choose `z in Y^(-1)(A)` with `Yz+C=Xtilde(h)`, possible since `A <= im(Y)`. The preceding containment puts `z in H`, and `Rz=Yz+C` lies in `im(Xtilde)`. Rank-poset agreement gives `Xtilde(z)=Rz=Xtilde(h)`. Consequently `h-z in ker(Xtilde)=B`, so `h in B+Y^(-1)(A)`. This proves `H=B+Y^(-1)(A)` directly.

Once `C` and `H` are fixed, `Xbar` is forced. Its pullback is zero on `B`; on `Y^(-1)(A)`, `R` takes values in `A/C` and rank-poset agreement forces `Xtilde=R`. Since `H=B+Y^(-1)(A)`, these values determine `Xtilde` everywhere and therefore determine `Xbar`. This establishes uniqueness. If `Y` is not ordinarily selected, the reverse implications above show no admissible triple can exist.

### Index triples versus active triples

The displayed sum indexes all triples with `C <= A`, `H >= B`, and `Xbar:H/B ~= A/C`. The count below is for this entire index set. For a fixed frequency `Y`, the active triples are exactly those also satisfying the hybrid selector and `Xtilde <=_r R`; the forward/reverse proof shows there is one active triple precisely when `Y` is ordinary-selected. Keep those two sets distinct in any Lean statement. In particular, do not bake a `Y(B)` incidence into the count's index or identify `Xbar`, `Xtilde`, and `R`.

## Exact inverse and the `2^(i*j)` count

The unconditioned index triples in (T1) are in bijection with all linear maps

```
theta : A -> W/B,
i = dim(A), j = dim(W/B) = codim(B).
```

Given a triple, define

```
theta = (H/B -> A/C)^(-1) o (A -> A/C).
```

Then `ker(theta)=C` and `im(theta)=H/B`. Conversely, given `theta`, set `C=ker(theta)`, let `H` be the inverse image of `im(theta)` under `W -> W/B`, and let `theta_bar:A/C -> H/B` be the induced isomorphism. Set `Xbar=theta_bar^(-1)`. These operations are mutual inverses: both recover the kernel, image, induced quotient map, and then its inverse. This includes `theta=0`, where `C=A`, `H=B`, the quotient spaces are both zero, and the unique zero-space isomorphism is used. It also covers `i=0` or `j=0` without an exception. Since an `i`-by-`j` binary matrix has `2^(i*j)` choices, the number of triples is exactly `2^(i*j)`.

The count is of all index triples, not just the triples active at a fixed frequency. The selector/rank-poset proof above establishes that each selected `Y` activates exactly one triple and each unselected `Y` activates none. This distinction is necessary when expanding the sum.

## Common physical carrier, phase, and output frequency

The first derivative `D_(C,H,T)` acts on the restriction carrier `Hom(V/C,H)`. Applying the rank derivative from `Xbar:H/B -> A/C` leaves the carrier

```
Hom((V/C)/(A/C), B).
```

The physical left side acts on `Hom(V/A,B)`. Identify the two domains using the canonical quotient map

```
(V/C)/(A/C)  ~=  V/A,       (v+C)+(A/C) |-> v+A.
```

Its inverse sends `v+A` to `(v+C)+(A/C)`. Both maps are well defined because `C <= A`, and are inverse by evaluating representatives. Transport a nested-carrier map `N : (V/C)/(A/C) -> B` to the physical carrier by `N o phi^(-1) : V/A -> B`, where `phi((v+C)+(A/C))=v+A`. This transport is essential: (T1) is an equality of functions on the actual `Hom(V/A,B)` carrier, not merely an equality of formal Fourier coefficient lists on differently parenthesized quotients.

For every active frequency `Y`, cyclic trace pairing gives the same affine phase on both sides, `chi_Y(T)`, and the same output frequency `q_A o Y|B : B -> V/A`. Indeed the restriction/quotient map on the right is `q_C o Y|H` followed by the induced `Xbar` derivative; on representatives `b in B`, the pulled-back `Xtilde` vanishes and the residual map is exactly `Yb` modulo `A`. Thus the common carrier transport above preserves evaluation at every input map and the character exponent. No orthogonality argument is involved. Expanding all finite sums and reindexing by the proved bijection gives (T1), even if distinct active terms elsewhere have equal output frequencies: finite sums preserve multiplicity and phase under a bijective reindexing.

## Relationship to the all-finite-complex A7 argument

This T1 step is used for arbitrary finite-dimensional `F_2` spaces and complex-valued `f`; it is not a scalar-real-only lemma. The surrounding target remains

```
||f||_4^4 <= 2^(100 D^2) Q(f),
Q(f) = sum over all actual hybrid (A,B), including (0,W), of
      E_T[ ||D_(A,B,T) f||_2^4 ],
```

for every finite ambient pair and degree bound `D`, with simultaneous induction on degree `D` across all finite spaces. The T1 count is `2^(i*j)` and Holder contributes its cube `2^(3*i*j)`; neither changes the target's unweighted all-hybrid `Q`, the induction variable, or the zero-order endpoint. This note does not discharge T2, the mixed/ordinary degree bookkeeping, the actual-graph count, W6 aggregation, or the final A7 theorem.

## Existing Lean interfaces and precise remaining implication

Read-only interface inspection found:

- `ActualBinaryMatrixHC46DR6Convolution.lean`: `DR6OrdinarySelected` states the ordinary image/kernel selector, and `DR6OrdinaryFilter` is its Fourier filter. The file documents that this differs from the hybrid `ambientHybridFilter`.
- `ActualBinaryMatrixHC46DR6Incidence.lean`: `DR6ComplexOrdinarySelected` exposes image inclusion and the dual-annihilator range condition; `dr6_complexSelector_iff_actualOrdinary` proves its equivalence to the ordinary selector. Its complex-filter coefficient lemmas support exact coefficient selection.
- `BinaryMatrixA1Composition.lean`: `ambientHybridFilter`, `initialDerivative_eq_restrict_hybridFilter`, and `manuscript_A1_restrict_filter` prove hybrid selector composition and carrier restriction for nested subspaces.
- `BinaryMatrixA1Complex.lean`: `complexAmbientHybridFilter` and `manuscript_A1_complex` lift that A1 composition to complex-valued functions.
- `ActualTypedABHybridSelectorSteps.lean`: line/hyperplane selector-step lemmas provide special cases, not arbitrary-subspace T1.

These interfaces do not establish the T1 theorem. A Lean closure must still provide, at minimum:

1. An arbitrary-subspace `C,H` construction with exact types `C=Y(B) intersect A`, `H=B+Y^{-1}(A)`, and the map `Xbar:H/B ~= A/C` plus its pullback `Xtilde:H -> V/C`.
2. The forward and reverse selector/rank-poset equivalence, including the reverse incidence that forces `C <= Y(B)`, uniqueness of all three data, and the no-active-triple result for unselected `Y`.
3. The inverse `theta <-> (C,H,Xbar)` as an actual finite equivalence (including zero-dimensional cases) and the cardinality `2^(i*j)`.
4. A typed proof that the nested quotient carrier is canonically `Hom(V/A,B)`, with representative-level evaluation and trace-phase/output-frequency equality. A1's nested-carrier equivalence is related infrastructure but is not by itself this T1 carrier calculation.
5. The actual finite Fourier expansion/reindex proving (T1) on that carrier. It must retain multiplicity and must not use orthogonality to discard frequency collisions.

Until these implications are implemented and kernel-checked, the derivation is a reviewed-candidate argument only. It makes no claim that the complete A7 target has been proved.
