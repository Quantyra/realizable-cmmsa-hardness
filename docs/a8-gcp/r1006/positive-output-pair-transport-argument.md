# S3132 positive output-pair transport argument

> **Superseding review correction (2026-10-04):** the initial `MANUSCRIPT GAP`
> verdict and two calculations below are not authoritative. The independent
> r1006 proof-adversarial and complexity reviews establish that the existing
> T2/A1 route controls cross terms by an `N^3` norm bound and needs no new
> manuscript hypothesis. The correct graph exponent is
> `N = 2^(k*(dim P + dim K - dim Q0))`, and the zero share is `||g||_2^4`.
> See `reviews/proof-adversarial.md`, `reviews/complexity.md`, and
> `route-decision.md`. This original note is retained as audit evidence of the
> rejected diagnosis.

Date: 2026-10-04. Scope: mathematical audit of the exact A8 output-
`Q` to actual A9 predecessor-sum step. No Lean or compiler execution was
performed.

## Verdict

**MANUSCRIPT GAP.** The subspace reindexing itself is explicit, surjective,
and has computable graph fibers. The T2 selector/complement correspondence
is bijective for each selected frequency. What is not proved by the inspected
manuscript or declarations is the normalized contribution identity joining
those two facts: for arbitrary complex `f`, the square of each output
pair's affine-filter mean must be sent, after the T2 expansion and finite
averaging, to the actual A9 output-energy summands. The present declarations
prove the component coordinate identity and the selector/frequency facts
separately; neither is that identity. Thus the desired inequality is not
refuted, but the proposed route has an unproved central equality/inequality.

## Carriers and canonical maps

Write `U = V/C`, `H = t1AmbientH t.K`, `X = t1PullbackMap t : H → U`,
`R = range X`, `K = ker X`, and let `q : V → U` be the quotient map.
The output carrier in `a7OutputBinary` is canonically equivalent, by
`t1OutputEquiv`, to

\[
 E=U/R \quad\hbox{and}\quad K=\ker X,
 \qquad \operatorname{Hom}(E,K).
\]

This is the quotient/kernel carrier, not an arbitrary coordinate space:
`t1OutputDomainEquiv`, `t1OutputKernelEquiv`, and
`t1OutputEquiv_physicalSquare` give the identifications; the coordinate
versions are `a8_output_coordinate_eq` and
`a8_carrier_coordinate_nested_filter`.

The pair indices of the output `a7HybridQ` are **all**
`P ≤ E` and `Q₀ ≤ K`. Here `P` is the output-side domain subspace and `Q₀`
the output-side range subspace. They correspond to actual A8 final pairs
as follows. Let `π : U → E` be the quotient. Put

\[
 L=q^{-1}(R)=(range X).comap(q),\qquad
 \bar A'=q(A'),\qquad Q₀'=B'\cap K.
\]

An actual final pair satisfies
`C ≤ A'`, `B' ≤ H`, `A' ∩ L = C`, and `B' + K = H`.
Its output pair is

\[
 P=π(\bar A'),\qquad Q₀=B'\cap K.
\]

Since `\bar A' ∩ R=0`, `π|_{\bar A'}` is injective. Since `B'+K=H`,
the restriction `B' → H/K` is onto and has kernel `Q₀`. Conversely, for
any `P ≤ E`, choose a linear section `s:P → U` of `π` over `P`, and set
`A'=q^{-1}(s(P))`; for any `Q₀ ≤ K`, choose a section of
`H/Q₀ → H/K` and let `B'` be its image in `H`. These produce exactly the
two A8 conditions. This describes existence; the choices are not canonical.

The actual A9 predecessor datum over this pair is not just `(A',B')`:
it is the genuine
`(A0,B0,X0)` with `A0 : A9AmbientA0 V A' i`,
`B0 : A9AmbientB0 W B' j`,
`X0 : B0.1 → V/A0.1`, `rank X0=k`, and the equation

\[
 a9AmbientFinalMap\ A'\ B'\ A0\ B0\ X0=Y',\qquad
 a9AmbientFinalMap=(q_{A0,A'} )\circ X0\circ incl_{B',B0}.
\]

In the fixed-T1 slice under audit, `A0=C`, `B0=H`, and `X0=X`; hence the
actual summand's final map is exactly
`a9AmbientFinalMap A' B' ⟨C, C≤A'⟩ ⟨H, B'≤H⟩ X`. In the full A9 source,
`A0,B0,X0` vary and the equation `induces` is retained, as in
`A9AmbientInitialDatum` and `A9AmbientFixedFinalFiber`.

The canonical T1 triple attached to a rank-`k` predecessor map is its
image/kernel factorization: take the image subspace in its codomain and the
kernel in its domain; the induced map from domain/kernel to image is an
isomorphism. Its inverse is the `theta` map `A → W/B` used by
`t1MapToTriple`; applying `t1MapToTriple` recovers the kernel and range,
while `t1TripleToMap_mapToTriple` and `t1MapToTriple_CK_roundTrip` give the
round trips. For the fixed slice, the already-given `t` supplies this
canonical data and `t1PullbackMap t` is its actual ambient representative.
For a general A9 datum the same construction is made on its actual quotient
and subspace carriers, not by selecting bases or a substitute matrix.

## Fibers, normalization, and the unproved step

The preceding map from actual A8 pairs to output pairs is surjective but
not injective in general. Over `P`, the possible `\bar A'` are sections of
`π` over `P`; they form an affine space over `Hom(P,R)`, of size
`2^(k·dim P)`. Over `Q₀`, the possible `B'` are sections of
`H/Q₀ → H/K`; their fiber is affine over `Hom(H/K,K/Q₀)`, of size
`2^(k·(k-dim Q₀))`. Thus the pair fiber has size

\[
 2^{k(\dim P+k-\dim Q₀)}.
\]

These are exactly the graph choices described in manuscript T2 (the two
complement counts `2^(ku)` and `2^(kv)`, with `u=dim P` and
`v=k-dim Q₀`). They are nonempty for every pair because finite-dimensional
quotient maps split. The choices are generally multiple, so a bare
output-pair-to-actual-pair map is not a bijection.

For clarity the denominators are as follows. Over `F₂`,
`|Hom(V,W)|=2^(nd)`, so the outer `typedUniformMean` over `T` divides by
`2^(nd)`. For an output pair `(P,Q₀)`, its inner `carrierMean` ranges over
`Hom(E/P,Q₀)` and divides by
`2^((dim E-dim P)·dim Q₀)`; `typedW6QComponent` squares that mean. Thus
`a7PairShare P Q₀ (a7OutputBinary t T f)` is the outer average over `T`
of this square. An actual summand with final map `Y'` has
`typedW6OutputEnergy A' B' Y' g` equal to the normalized mean over
`Hom((V/A')/range Y', ker Y')`, with denominator
`2^((dim(V/A')-rank Y')·dim ker Y')`; `a9AmbientA8Energy` then squares
that energy and averages over the same `2^(nd)` bases `T`.

The finite Fubini identity available once the pointwise integrand has been
identified is simply

\[
 \frac1{|\mathcal T|}\sum_{T\in\mathcal T}
   \frac1{|\mathcal M|}\sum_{M\in\mathcal M}g(T,M)
 =\frac1{|\mathcal T||\mathcal M|}
   \sum_{(T,M)\in\mathcal T\times\mathcal M}g(T,M)
 =\frac1{|\mathcal M|}\sum_M
   \frac1{|\mathcal T|}\sum_T g(T,M).
\]

Every affine translation or linear equivalence used to change `M` must be
shown bijective on the precise finite carrier; then its cardinality
denominator is preserved. `a8_carrier_coordinate_nested_mean` proves this
kind of normalized transport for one already-specified carrier function.
`a7_mixed_coordinate_pair_avg_eq_original` proves an averaged pair-share
identity for the mixed coordinate. Neither identifies the integrand after
the T2 expansion with the actual `Y'`-energy for every `(P,Q₀)` and every
graph lift. The frequency expansions `t2_left_derivative_expansion` and
`t2_right_derivative_expansion` only identify selected Fourier sums.
`t2_left_to_right`, `t2_right_to_left`, and `t2_complement_unique` prove
the selector/complement bijection for those frequencies, not for the
squared affine-filter means. Squaring a Fourier-sum identity does not
license termwise transport: cross terms and coalescing frequencies remain.
This is the precise missing compatibility for arbitrary complex `f`.

The required Lean-ready missing lemma is therefore a **single full-share
identity/inequality**, with no abstract contribution parameter: for the
`C,H,X` above and supported arbitrary complex `f`, prove after the exact
outer `T` average (or pointwise in `T` followed by that average) that the
sum over all `(P,Q₀)` of its actual `typedW6QComponent` terms is at most
`(2 : Real)^(6*D*k)` times the sum over the actual A8 pairs `(A',B')` of
`(typedW6OutputEnergy A' B' (a9AmbientFinalMap A' B' A0 B0 X)
  (filteredCarrierFunction A' B' T f))^2`, with the graph-lift multiplicity
and the exact carrier cardinalities accounted for. The pointwise proof must
use the T2 selector/complement bijection inside the full affine-filter
expressions, identify their translated bases, and then apply finite Fubini.
Average the resulting inequality over `T`; only after that reindex the
actual A8 source by `a9AmbientA8PartitionEquiv` and apply
`a9Ambient_A8_sum_partition`. This states the absent bridge directly in
the existing objects. The current files contain no such theorem.

## Zero class, positive classes, and the factor

The zero output pair is `(P,Q₀)=(⊥,⊤)`. Its share is the zero-order output
share; `a7_output_zero_share_eq_l2` and `a7_output_binary_l2_sq` identify it
with the output's fourth moment. Under the actual-pair map it has
`A'=C` and `B'=H` when `k>0` (the unique lift of `P=⊥`; the `Q₀=K`
section is `H`). It must first be transported with its own normalization.
Every other pair, including pairs with just one nontrivial coordinate, is
positive and must be included. `a7_pair_shares_exhaust` recombines the zero
share and every positive share into the complete `a7HybridQ`; the separate
zero-share results and `a7_outer_hybrid_energy_sq_le_complement_shares`
do not bound that positive sum. In particular, the latter is an outer
selected-filter bound, not a complete output-`Q` transport.

There are two distinct appearances of powers of two. Manuscript (A8)'s T2
graph choices have product `2^(k(u+v))`; the fourth-power comparison is
bounded there by `2^(3dk) ≤ 2^(6dk)` (and the text then uses its ambient
degree bound). In the Lean W6 normalization, each actual rank-`k` output
term is weighted by `2^(-6Dk)` inside the weighted moment sum. Clearing
that denominator is the exact algebraic source of the requested outer
factor `2^(6Dk)`. The equality
`2^(6Dk)·(2^(-6Dk)·E)=E` is exact; the comparison of graph multiplicity
and the manuscript's coarse exponential budget is an inequality. The
factor is not an injectivity correction, and it does not itself prove the
missing share identity. `a9Ambient_fixed_fiber_exact_charge` charges the
actual fixed-final fiber by its exact cardinality; its coarse version uses
the separate bound `2^(3D(i+j+k))` and requires the supported window.

## Edge cases and scope checks

- **`k=0`.** Then `R=0`, `K=H`, every output pair has a unique actual lift:
  `A'=q^{-1}(P)` and `B'=Q₀`. Both graph exponents are zero. The zero
  output pair maps to `(C,H)`. Positive output pairs still exist and cannot
  be dropped. The external factor is `1`.
- **Zero output pair.** As above, it is retained and uses the zero-share
  identities. Those identities alone do not settle the positive classes.
- **Empty/nonempty complement fibers.** The section fibers are always
  nonempty for these finite vector-space quotients; their exact sizes are
  the graph powers displayed above. A filtered frequency selector may,
  separately, select no frequencies; in that case its Fourier sum is zero,
  not an excuse to omit a pair class from `a7HybridQ`.
- **Truncated subtraction.** `D - a6Order t` is ordinary Nat subtraction.
  The support/degree argument needs `horder : a6Order t ≤ D`; with it,
  subtraction is exact. Without it, the result truncates to zero and does
  not encode the intended residual degree. The required theorem has this
  hypothesis.
- **`a+b+k>D`.** The multiplicity estimate
  `a7_a9_multiplicity_le` is only available under `a+b+k≤D`. Outside that
  window one must use the supported complementary-vanishing result to
  show the corresponding actual output energy is zero; one cannot apply
  the coarse count bound. The output-pair bridge itself must not silently
  impose the window as a stronger premise.
- **Arbitrary complex `f`.** All share and affine-filter identities must
  hold before specializing to characters. T2's frequency expansion is
  available for general Fourier coefficients, but a character-only
  comparison is insufficient to identify the squared normalized means.

## Existing declarations and next proof order

1. First target: author the full normalized output-pair/A8-summand bridge
   just stated, for arbitrary supported complex `f`, including every
   `(P,Q₀)` and every actual graph lift. Expand the actual
   `typedW6OutputEnergy` formula; do not introduce a proxy.
2. Use `a7_pair_shares_exhaust`, `a8_output_pair_component_nested_mean`,
   `a8_w6_domain_quotient_square`, and the T1 physical carrier square to
   establish its coordinate and denominator equalities.
3. Prove the bridge's per-frequency selector reindexing using
   `t2_left_derivative_expansion`, `t2_right_derivative_expansion`,
   `t2_left_to_right`, `t2_right_to_left`, and `t2_complement_unique`;
   add the missing affine-filter/squared-mean compatibility rather than
   citing selector equivalence as if it already implied it.
4. Perform the finite Fubini step with the cardinalities above, then
   average over `T` and use `a9Ambient_A8_sum_partition` to obtain the
   exact actual predecessor sum. The `6Dk` factor is cleared from the W6
   weight at this stage.
5. Only after this theorem, compose the supported-window multiplicity and
   complementary-vanishing bounds to recover analytic A8.

The fixed-final A9 partition equivalence and exact/coarse fiber charges in
`ActualBinaryMatrixHC46A9AmbientReindex.lean` are valid downstream
reindexings; they do not fill step 1. The r1006 route adjudication correctly
keeps this inside S3132 and does not trigger a literature-route reassessment:
the intended T2/A1 mechanism has not changed. The r1006 author reports
likewise record the absent pointwise contribution compatibility. No
counterexample to the final inequality follows from this audit; the
minimal outstanding proof obligation is the full-share bridge above.

## Required accounting

| Item | Status |
|---|---|
| Compiler | **NOT RUN** |
| Bounded increment | **NOT AUTHORED / NOT ACCEPTED** |
| Owning story S3132 | **PARTIAL** |
| Full-manuscript S3137 | **INCOMPLETE** |
| Accepted helper count | **2** |
