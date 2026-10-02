# A7 critical argument: mathematical route and Lean interface audit

Status: argument/interface audit authored for independent mathematical review. It is not a Lean proof, a validated roadmap, or a claim that A7 is certified. No implementation, module, compiler, or Git work was performed for this note. Scope is the manuscript argument at `paper/submission-manuscript.md`, approximately lines 1617-1811, together with the current DR6/A7 interfaces inspected on 2026-10-02.

## Target and scope

The target is the simultaneous dimension induction, for every pair of finite binary-matrix dimensions `n,d`, every complex-valued `f : BinaryMatrix n d -> Complex`, and every natural Fourier cutoff `D` with `ComplexFourierSupportedThrough D f`:

`uniformMean (fun M => Complex.normSq (f M)^2) <= 2^(100*d^2) * Q_D(f)`

where `Q_D(f)` is the sum of actual ordinary selected-complement derivative energies over all actual ambient `(A,B) != (0,whole)` with manuscript weight `2^(24*D*(dim A + codim B))`. The induction has no scalar-F2 premise. The `D=0` case is internal to the induction and is handled by Fourier inversion/constancy; it is not an extra assumption. Positive `D` uses strict degree decrease. Every sum is over the literal finite spaces/subspaces/matrices, not a proxy carrier.

The current full-scope DR6 endpoint is separately present as `dr6_actual_complex_fourth_moment_over_162_le` in `ActualBinaryMatrixHC46DR6Moment.lean`: arbitrary `n,d,D`, complex `f`, Fourier support only, and unrestricted actual nonzero `(A,B)` weighted ordinary-filter energy on the right. Its existence does not certify the manuscript's A7 proof route or the selector/induction steps below. The current accepted F2 incidence result is a distinct ingredient and is not an A7 premise.

## T1: ordinary selector to the unique hybrid selector

Fix actual subspaces `A <= V`, `B <= W`, and an actual matrix/frequency `Y` satisfying the ordinary selector `A <= im(Y^T)` and `ker(Y^T) <= B`. Define

- `C = im(Y^T) intersect A`;
- `H = B + (Y^T)^-1(A)`;
- `R : H/B -> A/C` by `R(b+z) = Y^T z + C`.

The proof obligations are: (i) `R` is well-defined; (ii) `ker R = 0` and `im R = A/C`, hence it is an isomorphism; (iii) the ordinary frequency `Y` is selected by the hybrid selector indexed by `(C,H,R)`; and (iv) this triple is unique for the fixed `(A,B,Y)`. Conversely, a hybrid-selected frequency for a valid triple must satisfy the ordinary selector. For that frequency, `im(Y^T)/C` and `A/C` give the complementary image decomposition used to recover `R` and the ordinary pair. This converse prevents a hidden multiplicity from being discarded.

At the level of the manuscript sum, the selector identity is

`R_{A,B,T} P_{A,B} f = sum_{C<=A,H>=B,X:H/B ~= A/C} D_X D_{C,H,T} f`.

The same frequency contributes the same character phase `chi_Y(T)` on both sides, and the output frequency is `q_A Y^T|B`. Thus the identity is a pointwise finite-sum regrouping, not an orthogonality claim. The parameter triples are in bijection with linear maps `theta : A -> W/B`, by `C=ker theta`, `H/B=im theta`, and the induced isomorphism `X`; consequently their number is `2^(i*j)`, `i=dim A`, `j=codim B`. Holder on this exact number of terms costs `2^(3*i*j)`.

Ordinary/hybrid names currently found: `DR6OrdinarySelected` and `DR6OrdinaryFilter` in `ActualBinaryMatrixHC46DR6Convolution.lean`; the complex incidence counterpart is `DR6ComplexOrdinarySelected` with an equivalence to the ordinary predicate in `ActualBinaryMatrixHC46DR6Incidence.lean`. Those interfaces express the ordinary selector. This audit did not find a theorem giving the full arbitrary-actual-subspace T1 equivalence, uniqueness, or the pointwise ordinary-to-hybrid derivative identity in those interfaces. Exact selector-indexed derivative and quotient-map bridge statements remain to be named and proved in the target Lean surface.

The dimension bookkeeping after T1 is: for nonzero ordinary `(A,B)`, `i,j <= d`; if `t=dim C + codim H + rank X`, then `i+j=t+rank X <= 2t`; hence `7*d*(i+j)+3*i*j <= 10*d*(i+j) <= 24*d*t`. This yields the manuscript A6 bound with exponent `24*d*t`. The two rank-lowering formulas make the mixed derivative zero when `t>d`. These exact endpoint/zero statements must be retained; no conditional substitute is used here.

## T2: both selector directions and uniqueness for arbitrary actual S,T

For an arbitrary actual map/frequency `X` of rank `k`, put `A1=im(X^T)`, `B1=ker(X^T)`. A hybrid-selected `Y` is parameterized by actual complements `A2=A1 direct-sum C`, `H+B1=W`, `H intersect B1=B2`, and induced `X'=q_C X^T|H`. The identity to prove is

`D_{A2/A1,B2,T}(D_{X,S} f) = sum_{C,H} D_{X'} D_{C,H,S+j_{B1} T q_{A1}} f`.

Both selector directions are required. In the forward direction, if `X` precedes/selects `Y`, set `Z=Y-X`. Rank additivity gives disjoint images and kernel/image dimension identities. The hybrid conditions force `C=im(Z^T) intersect A2`, complementary to `A1`, and force `ker(Z^T)+B2 <= H`; `ker(Y^T)<=B2` then supplies the needed containment. In reverse, the right-hand selectors imply `im(X^T)<=im(Y^T)`. If `Y^T w` lies in `im(X^T)`, quotient matching supplies `h in H` with the same `Y^T` image after the `C` correction; `w-h` lies in `ker(Y^T)<=H`. The hybrid rank-poset equality then gives `Y^T w-X^T w` in `C intersect A1=0`, so `X` selects/precedes `Y`. Set `Z=Y-X`.

Uniqueness uses the exact restriction-plus-quotient rank losses. Hybrid rank drop and `rank X'=rank X=k` force equality in the loss bound, hence `ker(Z^T)<=H` and `C<=Z^T(H)` (equivalently the preimage containment required by the quotient map). Disjointness from `A1` yields `C=im(Z^T) intersect A2`. Also `ker(Z^T)+B2<=H`; its intersection calculation uses `B2<=ker(X^T)` and `ker(Y^T)<=H intersect B1=B2`, so the intersection is `ker(Y^T)`. Rank-nullity shows equal dimensions and therefore `H=ker(Z^T)+B2`. These force the parameters uniquely. The phase on both sides is the same `chi_Y(S+j_{B1} T q_{A1})`, and the frequency on both sides is `q_{A2}Y^T|B2`. Frequencies may collide; the proof is equality of grouped finite sums with multiplicities, not orthogonality or distinct-frequency cancellation.

Current related Lean surfaces include `w6Precedes` and the actual W6 derivative/frequency fiber in `ActualBinaryMatrixHC46A7WeightedPredecessor.lean`; `w6_precedes_transpose_range_decomposition`, `w6_precedes_transpose_kernel_intersection`, and `w6_precedes_restriction_surjectivity` establish rank-additive linear-algebra consequences. The actual carrier frequency is `w6ActualCarrierFrequency`, with literal fiber `w6ActualPredecessorFrequencyFiber`. These are useful ingredients, but they are not the T2 statement: no inspected interface packages both selector directions, arbitrary actual `(S,T)` phase transport, uniqueness of `(C,H)`, and the stated finite-sum derivative identity. `w6_predecessor_descended_idempotent` is not a replacement for that selector identity.

## Simultaneous strict-degree induction and D=0

Induct simultaneously over all finite spaces by their dimension `d`; quantify over all complex functions and all cutoffs at each dimension. Base dimension zero is included. For cutoff `D=0`, support says all nonzero frequencies vanish; Fourier inversion makes `f` constant. The zero-order derivative term in `Q_D` gives equality/controls the fourth moment. Do not assume `D>0` globally.

For positive `D`, take a term in A6 with initial ordinary dimensions `s=dim A0+codim B0`, rank `k=rank X`, and `t=s+k>0`. The first mixed derivative has Fourier degree at most `d-t`, strictly smaller than `d`; apply the simultaneous induction hypothesis to that actual derivative on its quotient/restricted finite space. Its derivative order is `u+v <= d-t`. This strict decrease, including all intermediate dimensions, is the induction measure. The moment source's separate `D=0` branch confirms the style of support-zero inversion for the DR6 endpoint, but it is not itself this A7 simultaneous induction theorem.

## A8: mixed order versus ordinary order

Apply T2 once for each of the two derivative slots, summing over the actual complements. For quotient rank `k`, each complement graph family has exactly `2^(k*u)` or `2^(k*v)` choices, so the fourth-power/Holder cost is at most `2^(3*d*k) <= 2^(6*d*k)` under `u+v<=d-t`. The derivative on the original ambient matrix is ordinary selected-complement order

`s + 2*k + u + v`,

which can exceed `d`; it must not be asserted to be at most `d`. The mixed induction restriction is instead

`s + k + u + v <= d`.

The A8 sum is over actual `A>=A0`, `B<=B0` with `A intersect A1=A0`, `B+B1=B0`, and term `D_{X|B mod A} D_{A,B,T} f`. Quotient identification `(V/A0)/(A/A0) ~= V/A` is canonical. Each final `(A,B)` reconstructs the intermediate pair uniquely as `(A+A1, B intersect B1)`. The translate remains uniform by the canonical embedding and Fubini, with no extra rank/cardinality factor. This mixed-vs-ordinary distinction is a central obligation: replacing the mixed bound by an ordinary-order cutoff would be false in general and would invalidate induction.

Current modules expose actual derivative/carrier operations, but this audit did not find a theorem matching the two T2 applications followed by the unique reconstruction and the mixed-order bound. That assembly remains an explicit proof step.

## A9: actual graph predecessor count

Fix final actual `(A,B,Y)` with `a=dim A`, `b=codim B`, `k=rank Y`, and initial dimensions `i=dim A0`, `j=codim B0`. The mixed constraint is `i+j+k<=d`. Count actual initial triples inducing this fixed final data by

`[a choose i]_2 [b choose j]_2 2^(k*(a-i)) 2^(k*(b-j))`.

The Gaussian factors choose actual subspaces. The first graph factor chooses a lift of `im(Y^T)` to `V/A0` disjoint from `A/A0`; the second chooses a kernel complement in `B0/ker(Y^T)` to `B/ker(Y^T)`. Projection along the chosen kernel followed by `Y^T` and the unique lift determines `X`; verify that this construction preserves rank and gives the claimed final `(A,B,Y)`. Conversely every initial triple yields exactly those graph data. This is an actual graph/rank count, not a proxy Grassmann bound or a guard such as `Grass(n-j)/j<=n`.

A conservative consequence used in A9 is a multiplicity at most `2^(3*d*(i+j+k))`. Current related interfaces include `w6_card_rank_k_predecessors`, `w6_rank_k_predecessors_le_four_pow`, and the actual fixed-frequency fiber formula `w6_actual_predecessor_frequency_fiber_card` (`2^(2*rank(X)*rank(Z))`). They count actual predecessor matrices or fixed-frequency collision fibers, respectively. Neither statement alone is the A9 count over initial/final actual subspace triples; the graph decomposition above and its bijection/count must be explicitly connected to the induction aggregation.

## A10/A11: full W6 aggregation with one common D

For each final actual derivative input, use the W6 weighted fourth-moment estimate with the same outer cutoff `D` (not a local changing cutoff). Combining A8, A9, and the A6 coefficient gives, for `t=i+j+k in [1,d]`, exponent

`100*(d-t)^2 + 27*d*t + 6*d*k <= 100*d^2 - 63*d*t - 4*d*k`.

The `27*d*t` comprises the A6 weight and the conservative A9 multiplicity; `6*d*k` is the two-complement graph/Holder cost. After factoring `2^(100*d^2)`, the remaining coefficient is bounded by `2^(-31*d*(k+1))*2^(-4*d*k)` (with the manuscript's separate k=0, i=j=0 exclusion). Sum over actual ranks using `z=2^(-63*d)`: for `k>=1`, `sum_{i,j>=0} z^k/(1-z)^2 <= 2*z^k <= 2^(-31*d*(k+1))`; for `k=0`, omit `(i,j)=(0,0)` and use `(1-z)^(-2)-1 <= 4*z <= 2^(-31*d)`. The resulting actual W6 weighted sum is bounded by `2^(100*d^2+1-31*d) Q_D(f)`; the zero-order contribution is controlled by `Q_D(f)`. The endpoint check in the manuscript is `162*(2^(-94*d^2)+2^(1-31*d))<1` for `d>=1`, yielding the target after moving the left error terms. Dimension zero and `D=0` remain covered by the base/constant arguments.

Current A7 infrastructure includes:

- `complex_carrier_parseval` and `actualW6Derivative_energy_parseval` in `ActualBinaryMatrixHC46A7CarrierParseval.lean`;
- `actualW6Derivative_carrierCoeff_fiberSum`, the pointwise fiber Cauchy bounds, and `actualW6Derivative_fourierEnergy_fiber_partition` in `ActualBinaryMatrixHC46A7EnergyConsumer.lean`;
- `w6_actual_predecessor_frequency_fiber_card`, the exact actual collision-fiber count, in `ActualBinaryMatrixHC46A7WeightedPredecessor.lean`;
- `w6_card_rank_k_predecessors`, `w6_rank_k_predecessors_le_four_pow`, and `w6_weighted_rank_k_predecessor_sum_le` in `ActualBinaryMatrixHC46A7PredecessorCount.lean`;
- `actualW6Derivative_weighted_fourth_moment_le_67_63` and its weaker `..._le_two`, with common cutoff `D`, in `ActualBinaryMatrixHC46A7EnergyConsumer.lean`.

These establish substantial actual-carrier W6 estimates, including the `2` bound, but do not currently expose a theorem identified here with the manuscript A7 induction conclusion, nor the A6-to-A8-to-A9 mapping of every term and its coefficient. In particular, the A7 target uses a full-dimensional ordinary derivative-energy sum while the extant W6 result is a weighted sum of squared carrier means. Their exact normalization/aggregation bridge must be stated and checked in the implementation proof; the names or proximity of these theorems do not close that gap.

## Dependency ledger and unresolved implications

1. Ordinary selector <-> unique hybrid `(C,H,X)` at fixed actual frequency, both directions: not located as a complete current Lean theorem.
2. Pointwise complex derivative finite-sum identity preserving phase and multiplicities: not located as complete theorem.
3. T2 selector equivalence and uniqueness for arbitrary actual `S,T`, with possible frequency collisions and same-phase grouped sums: not located as complete theorem; rank-additive W6 linear-algebra lemmas are partial ingredients only.
4. Simultaneous all-dimension induction, including internal `D=0` inversion and strict `d-t<d`: not located as A7 theorem.
5. Two T2 transports yielding A8; precise mixed `s+k+u+v<=d` versus ordinary `s+2k+u+v`: must be formalized without strengthening the latter.
6. Actual graph bijection/count in A9: current actual predecessor and collision-fiber counts do not alone give the needed triple count.
7. Coefficient aggregation and common-`D` W6 normalization through A10/A11: must connect the manuscript terms to current estimates with exact constants and endpoints; the carrier-energy-to-target-energy normalization is an explicit check.
8. Terminal `162` endpoint and zero-dimensional cases: retain the manuscript inequalities and exact zero-order term; do not treat a nearby DR6 theorem or F2 incidence theorem as a substitute proof of A7.

## Evidence boundary

This is a mathematical route and interface audit for Root's sufficiency review. It records the full argument and the known proof obligations; it does not claim that every lemma has been validated against a kernel proof. No helper-count or file-count is reported as progress. No implementation or module was modified. A7 remains uncertified by this artifact pending independent mathematical review and subsequent formalization/build verification.