# Exact side-condition extension of one fixed-complement zoom

E002 / S3137. Mathematical derivation before translation, 2026-10-11.
This advances the last paragraph of the canonical manuscript's robust-local
lemma. It is not a Lean theorem, a native result, or an independent review.
The original fixed table and selected representative remain fixed throughout.

## Statement and source interface

Work over F_2 in a finite vector space U = H direct-sum A, with dim H = J
and dim A = n. Fix Q <= W' <= A, dim Q = a, codim_A W' = c and a <= d.
Assume the finite family Z' = {R <= W' : Q <= R, dim R = d} is nonempty.
Let T assign one linear functional T_D to each full domain D = H + R.
The same T_D must apply to every presentation of D. Assume the actual
canonical row-validity property: on the equation vectors spanning H, every
T_D takes the prescribed, fixed right-hand-side values. This is information
returned by the captured selected_physical_density_with_rows candidate,
not a property inferred from a bare TaggedLeafTable.

Fix g : W' -> F_2. The ordinary table on A is T_A(R) = T_(H+R)|R,
exactly the transportedLeafTable construction. Put W = H direct-sum W'.
There exists a linear G : W -> F_2 extending g and the side conditions,
with codim_U W = c and Q + H <= W. The exact agreement of g with T_A on
uniform Z' equals the agreement of G with T_(H+L)|L on the uniform family
Z = {L <= W : Q <= L, dim L = d, L intersect H = 0}.
Thus an original-table agreement at least epsilon'/2 is retained exactly,
and in particular remains at least C = epsilon'/5 for epsilon' >= 0.

Pinned interfaces to inspect for translation:

- ActualTaggedComplementStarDensityBridge.transportedLeafTable indexes
  the full domain H + R before restricting to R.
- ActualTaggedSelectedDecoderBridge.taggedSelectedDomainTable_apply and
  taggedSelectedLeafLabel_respectsRows supply the same canonical table's
  row validity for every actual presented leaf.
- ActualTaggedComplementIncidence.ordinaryFullEquiv is an existing
  full-domain/intersection bijection pattern. Its center-parameterized
  interface is not silently identified with this arbitrary advice Q zoom.
- ActualTaggedMZSideDraw supplies the actual transverse carrier definitions.

## The side functional is forced, not newly assumed

Choose R0 in Z', using the inverse witness's nonzero zoom cardinality.
Define lambda = T_(H+R0)|H. For every R in Z', T_(H+R)|H = lambda:
both linear maps take the same prescribed values on every equation vector,
and those vectors span H. Linear-map equality on a spanning family proves
equality on H. This does not require choosing another table or adding a
solvability assumption. In the source specialization, the span definition
and each presented leaf's row predicate must be unfolded to prove this
equality; an unproved compatibility premise is not a replacement.

Define G(h+x) = lambda(h) + g(x), for h in H, x in W'. The decomposition
is unique because H intersect A = 0. This defines a linear map and proves
both restrictions. Dimensions give dim W = J + dim W', hence the exact
codimension equality. The same proof works for every retained original-table
zoom; no claim concerns the randomly refreshed table's row validity.

## Explicit fiber bijection and constant multiplicity

Let pi : W -> W' be projection along H. For L in Z, pi|L is injective,
so R = pi(L) has dimension d, contains Q and lies in W'. Its inverse
identifies L with the graph of a unique linear phi : R -> H:

    L = {phi(x) + x : x in R},       phi|Q = 0.

The vanishing condition follows from Q <= L and Q <= W'. Conversely every
R in Z' and every linear phi : R -> H vanishing on Q gives such an L.
Both composites are identities on subspaces and maps. This is a bijection
between Z and the dependent sum of these map fibers over R in Z'. Each
fiber is naturally Hom(R/Q,H), of cardinality M = 2^(J*(d-a)).
It is strictly positive and independent of R, so projection sends the
uniform distribution on Z to the uniform distribution on Z'. In particular
Z is nonempty and |Z| = M*|Z'|. This also treats a=d and J=0 correctly.

## Event equality on every graph, then exact rational agreement

For L the graph of phi over R, H+L = H+R. Both T_(H+R) and G agree with
lambda on H. For every x in R,

    T_(H+L)(phi(x)+x) - G(phi(x)+x) = T_(H+R)(x) - g(x).

Consequently the two restrictions agree on L if and only if T_A(R)=g|R.
There is no choice of a label depending on phi: domain-indexing gives the
same T_(H+R) for the entire fiber. A numerator count therefore gives
|agreeing Z| = M*|agreeing Z'|. Cancel M in the rational cardinality ratios,
using M>0 and the recorded nonemptiness. Casting preserves the equality
over the reals. No total-variation subtraction or loss is needed at this
conditioned-transverse step. The later transition to an unconditioned leaf
law still needs its separately bounded nontransverse loss.

## Uniform advice marginal and the full-law correction

For completeness, the other complement-fiber count used immediately before
this extension is also exact. Uniformly choose a complement A of H and
then a uniform a-space Q <= A. The number of complements is 2^(Jn).
For any fixed Q disjoint from H, choose one reference complement containing
Q. All other such complements are graphs of maps from its n-dimensional
space to H that vanish on Q, so their number is 2^(J*(n-a)). Every complement
has the same number of a-spaces. Counting incidences proves the marginal of
Q is uniform among all H-disjoint a-spaces. This is an unconditioned
experiment over all complements; unsuccessful pairs remain in the sample
space. Existence of a successful complement for Q follows with probability
at least the joint success probability, without conditioning on success.

For Q uniform among all a-spaces of U, a union bound over nonzero vectors
of H bounds the intersecting fraction by

    delta <= (2^J-1)*(2^a-1)/(2^(J+n)-1) <= 2^(a+1-n),

where the last inequality holds for J+n>=1; the zero-dimensional case is
trivial. This uses the exact probability that a fixed nonzero vector belongs
to a uniform a-space. If a property holds on fraction p of H-disjoint
Q, it holds on fraction (1-delta)*p >= p-delta among all Q, since 0<=p<=1.
The selected dimension guards establish n>=5h^2+r+2 and a<=r, producing
exactly the previously recorded manuscript correction. No good-complement
renormalization or further change of Q law is allowed.

## Remaining implementation obligations and boundaries

Translate the graph/subspace bijections, their constant fiber cardinalities,
span-based side-functional equality, and event iff on the actual carriers.
Prove the actual presented-leaf construction for every R and graph L under
the already selected dimensions; the abstract argument does not fabricate
those source constructors. Compose with the canonical representative witness
and the original-table output of refresh amplification. Native GCP evidence,
axioms and mandatory review remain absent for these new arguments.

This supplies the side-extension and advice-law mathematical steps, not the
adaptive refresh construction, source NO promise, global decoder, encoded
runtime, hardness theorem or learning corollary. It does not change the
canonical manuscript. Remaining to-do list: actual-carrier translation and
native verification; robust amplification and same-joint-law decoder; the
unchanged full campaign certification obligations.
