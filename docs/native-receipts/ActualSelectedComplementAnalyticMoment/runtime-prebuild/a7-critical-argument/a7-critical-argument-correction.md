# A7 critical argument correction and authoritative audit

Status: this correction supersedes the mathematical statements and interface conclusions in `a7-critical-argument-audit.md`. That earlier file is retained unchanged as historical evidence (its SHA256 at capture was `54504b0a7fc05ba2d2e75401b15b69e1dbffe712494e08909f4d3b111a6cda3c`). It contains material errors identified in independent review: it used the wrong energy, conflated degree with ambient dimension, misstated the T1 intersection, and described the A8 cost route inaccurately. Use this correction as the current audit. Neither note is a proof or a certification. No implementation, Lean module, compiler, or Git work was performed.

Source re-read: `paper/submission-manuscript.md`, lines 1617-1812, plus the current selector/derivative/W6 interfaces listed below. Parameter convention here is explicit: `D` is the Fourier-degree bound and induction parameter. The finite ambient spaces may have arbitrary dimensions and vary simultaneously; those dimensions are not the induction parameter.

## Exact A7 target

For every pair of finite binary spaces, every complex `f` with Fourier support through degree `D`, prove

`||f||_4^4 <= 2^(100*D^2) * Q(f)`,

where

`Q(f) = sum over ALL actual hybrid pairs (A,B), including (0,whole), of E_T ||D_{A,B,T} f||_2^4`.

This is an unweighted hybrid derivative energy. It is not the weighted `2^(24*D*(dim A+codim B))` ordinary nonzero-pair energy used in the current DR6 endpoint. The cutoff is `D`, independent of either ambient dimension. A7 is simultaneous induction on `D` across all finite spaces. At `D=0`, only the zero-order term contributes and the manuscript says equality holds. No scalar-F2 premise is introduced.

The current DR6 theorem `dr6_actual_complex_fourth_moment_over_162_le` is a separate result with arbitrary complex input and support-only hypothesis, but its RHS is the weighted actual ordinary nonzero-pair energy and its left side has `/162`. It is not A7 and cannot substitute for this induction. Likewise, F2 incidence is not an A7 premise.

## T1: correct maps, both selector directions, and multiplicity

Fix actual subspaces `A <= V`, `B <= W` and an actual frequency/map `Y` selected by the ordinary selector `P_{A,B}`. Set

- `C = Y(B) intersect A` (not `im(Y) intersect A`);
- `H = B + Y^{-1}(A)`;
- `R = q_C Y|H : H -> V/C`;
- `X : H/B -> A/C`, defined by `X(b+z)=Yz+C` for `b in B`, `z in Y^{-1}(A)`.

These are different maps and must stay distinct. Well-definedness of `X` follows because a change in decomposition changes `Yz` by `Y(B) intersect A=C`. Its kernel is zero on `H/B`, and its image is all of `A/C`; hence it is an isomorphism. Also `Y^{-1}(C)<=B`, so the hybrid selector accepts `Y`. The images `Y(B)/C` and `A/C` are disjoint, and `R` maps onto their sum with `X` as its `A/C` component. This is the rank-additive relation `X preceq R` in the manuscript.

The reverse direction is essential. If an actual triple `(C,H,X)` has the stated kernel/image conditions, accepts `Y` by the hybrid selector, and `X preceq q_CY|H`, then the selector forces `A<=im Y` and `ker Y<=B`. Agreement on the preimage of `im X` gives `Y(B) intersect A<=C`; for `c in C`, a preimage in `H` and `ker R<=ker X=B` gives the reverse inclusion. For `Yw in A`, choose `h in H` matching modulo `C`; the hybrid preimage condition gives `w in H`. On `Y^{-1}(A)`, `R=X` and maps onto `A/C`, so `H=B+Y^{-1}(A)`. Its zero value on `B` and agreement on that preimage determine `X`. Therefore triples are unique and none exist for an unselected `Y`.

The exact finite-sum identity is manuscript (T1):

`R_{A,B,T} P_{A,B} f = sum_{C<=A,H>=B,X:H/B ~= A/C} D_X D_{C,H,T} f`.

For every actual frequency the surviving phase is the same `chi_Y(T)` and the final frequency is `q_A Y|B`; this is pointwise regrouping on the actual common domain, with no orthogonality assumption. Triples correspond bijectively to linear maps `theta:A -> W/B` by `C=ker theta`, `H/B=im theta`, and the induced isomorphism `X`. Thus the count is exactly `2^(i*j)`, `i=dim A`, `j=codim B`, and Holder on the sum costs `2^(3*i*j)` in fourth powers.

Under degree support through `D`, a nonzero ordinary term has `i,j<=D`. For `t=dim C+codim H+rank X`, `i+j=t+rank X<=2t`; hence the manuscript estimates `7D(i+j)+3ij <= 10D(i+j) <= 24Dt`. Reindexing by the unique original pair yields A6, with `/162`, a `2^(6D^2)||f||_2^4` term, and weighted mixed derivative fourth moments with factor `2^(24Dt)`. Terms `t>D` vanish by the two rank-lowering formulas. These are intermediate steps toward A7, not its statement.

Relevant current Lean interfaces: `DR6OrdinarySelected`, `DR6OrdinaryFilter` in `ActualBinaryMatrixHC46DR6Convolution.lean`; `DR6ComplexOrdinarySelected` and its equivalence with the ordinary selector in `ActualBinaryMatrixHC46DR6Incidence.lean`; `complexAmbientHybridFilter` and `manuscript_A1_complex` in `BinaryMatrixA1Complex.lean`; `ambientHybridFilter`, `initialDerivative_eq_restrict_hybridFilter`, and `manuscript_A1_restrict_filter` in `BinaryMatrixA1Composition.lean`; line/hyperplane selector steps in `ActualTypedABHybridSelectorSteps.lean`. These establish useful A1 or restricted selector facts, but the audit did not locate the full arbitrary-subspace T1 selector equivalence, uniqueness, and pointwise complex finite-sum identity with the corrected `C` and distinct `X`/`R` types.

## T2: both directions, equality cases, uniqueness, phase

For actual `X`, set `A1=im X`, `B1=ker X`, and let `A2=A1 direct-sum C`, `H+B1=W`, `H intersect B1=B2`, `X'=q_C X|H`. The manuscript identity (T2), for arbitrary actual bases/shifts `S,T`, is

`D_{A2/A1,B2,T}(D_{X,S} f) = sum_{C,H} D_{X'} D_{C,H,S+j_{B1}Tq_{A1}} f`.

Forward selector direction: from `X preceq Y` passing the left selector, put `Z=Y-X`. Rank additivity gives complementary images and `ker X+ker Z=W`. The hybrid conditions force `C=im Z intersect A2` complementary to `A1`, and `{w in B1 : Zw in C}<=B2`, including `ker Y<=B2`. Set `H=ker Z+B2`; it has the required complement properties, the right hybrid selector holds, and quotienting the two complementary image components gives `X' preceq q_CY|H`.

Reverse direction: the right selector gives `im X<=im Y`. If `Yw` lies in `im X`, the quotient image condition finds `h in H` matching modulo `C`; `C<=Y(H)` corrects the match to `Yh=Yw`. Then `w-h in ker Y<=H`. Rank-poset agreement modulo `C` gives `Yw-Xw in C intersect A1=0`, hence `X preceq Y`; put `Z=Y-X`.

For uniqueness, hybrid rank drop and `rank X'=rank X` give `rank(q_C Z|H)=rank Z-dim C-codim H`. Restriction plus quotient can lose at most that amount, so equality forces `ker Z<=H` and `C<=Z(H)`, equivalently the required preimage containment. Disjointness from `A1` forces `C=im Z intersect A2`. Also `ker Z+B2<=H`; the intersection is `ker Y` because `B2<=ker X` and `ker Y<=H intersect B1=B2`. Rank-nullity gives equality `H=ker Z+B2`. Thus parameters are unique and give the left selector. Both sides retain the same phase `chi_Y(S+j_{B1}Tq_{A1})` and output frequency `q_{A2}Y|B2`. This is grouped-sum equality even when frequencies collide, not orthogonality.

Actual current W6 ingredients include `w6Precedes`, `w6_precedes_transpose_range_decomposition`, `w6_precedes_transpose_kernel_intersection`, `w6_precedes_restriction_surjectivity`, `w6PredecessorRestrictedMap`, and `w6_predecessor_descended_idempotent` in `ActualBinaryMatrixHC46A7WeightedPredecessor.lean` / `ActualBinaryMatrixHC46A7PredecessorCount.lean`. These prove rank-additive linear-algebra structure, not the complete T2 equivalence, unique `(C,H)` transport, arbitrary `S,T` phase identity, or derivative sum. Those implications remain explicit obligations.

## Simultaneous induction and A8, with the correct cost route

Induct on Fourier degree `D` simultaneously over all finite spaces and all complex inputs. The `D=0` case is internal: support implies constancy by Fourier inversion, and the zero-order hybrid term in `Q(f)` gives equality. For `D>0`, A6 terms have initial pair `(A0,B0)`, rank-`k` map `X`, `s=dim A0+codim B0`, and `t=s+k>0`. The first mixed derivative has degree at most `D-t<D`; invoke the induction hypothesis on its actual smaller quotient/restricted space. A subsequent hybrid order `u+v` satisfies `u+v<=D-t`.

A8 is obtained by the manuscript's sequence: induction on the first mixed derivative, then T2, then A1. Do not describe this as applying T2 independently to two derivative slots. The complement graph count/cost used by the manuscript is at most `2^(3Dk)`, conservatively bounded by `2^(6Dk)`. The induced final ordinary derivative order is `s+2k+u+v`, which may exceed `D`; only the mixed inequality `s+k+u+v<=D` is valid. Keep these separate.

A8 sums over actual `A>=A0`, `B<=B0` with `A intersect A1=A0` and `B+B1=B0`, with term `D_{X|B mod A}D_{A,B,T}f`. Quotient identification is `(V/A0)/(A/A0)=V/A`. A final pair reconstructs the intermediate pair uniquely as `(A+A1,B intersect B1)`. The shift plus its canonical embedding is uniform; Fubini removes the inner average with no multiplicity or rank-conditioning factor. The exact displayed A8 coefficient is `2^(100(D-t)^2+6Dk)`.

Relevant current Lean modules expose A1 derivatives/filters and A7 W6 transport components, but this audit found no theorem implementing the full induction -> T2 -> A1 A8 identity, preserving the mixed bound while allowing the ordinary order to exceed `D`. This complete transport remains open.

## A9 actual graph count and nonzero endpoint

Fix final actual `A,B,Y`, with `a=dim A`, `b=codim B`, and `k=rank Y`; the nonzero final terms require `a+b+k<=D`. For initial dimensions `i=dim A0`, `j=codim B0`, the mixed constraint is `i+j+k<=D`. The exact number of initial triples inducing this fixed final data is

`[a choose i]_2 [b choose j]_2 2^(k*(a-i)) 2^(k*(b-j))`.

Choose actual `A0<=A` and `B0>=B`. The first graph chooses a lift of `im Y` to `V/A0`, disjoint from `A/A0`; the second chooses a kernel complement in `B0/ker Y` to `B/ker Y`. The selected kernel and projection, followed by `Y` and the unique image lift, determine `X` uniquely; prove this construction is inverse to extracting the graph data and preserves rank `k`. The count is at most `2^(D(i+j+k))`; the manuscript uses the conservative `2^(3D(i+j+k))`. This is an actual graph count, not a proxy Grassmann estimate or dimension guard.

Current related declarations include `w6_card_rank_k_predecessors`, `w6_rank_k_predecessors_le_four_pow`, and `w6_actual_predecessor_frequency_fiber_card`. They count actual rank-k predecessor matrices and actual fixed-frequency collision fibers, not the A9 initial-triple count. The graph bijection and its count still need to be connected to the induction terms. The final nonzero support bound `a+b+k<=D` must remain distinct from the initial mixed bound.

## A10/A11 aggregation, common cutoff, and endpoint

Set `t=i+j+k`, with `1<=t<=D` for the nonzero A6 terms. A6, A8, A9 give

`100(D-t)^2 + 27Dt + 6Dk <= 100D^2 - 73Dt + 6Dk <= 100D^2 - 63Dt - 4Dk`.

For `k>=1`, put `z=2^(-63D)` and sum over `i,j>=0`: `z^k/(1-z)^2 <= 2z^k <= 2^(-31D(k+1))`. For `k=0`, omit `i=j=0`; `(1-z)^(-2)-1 <= 4z <= 2^(-31D)`. This gives manuscript A11 with leading `||f||_4^4/162`, first term `2^(6D^2)||f||_2^4`, and the actual sum over `A,B,Y` of rank `k`, `|(A,B)|+k>0`, coefficient `2^(-31D(k+1))*2^(-4Dk)`, and `E_T||D_Y D_{A,B,T}f||_2^4`.

Rewrite the coefficient as `2^(-31D-29Dk)*2^(-6Dk)`. Apply the manuscript W6 bound with the one common cutoff `D` to each actual `D_{A,B,T}f`, and enlarge sums by nonnegativity; the last-line contribution is at most `2^(100D^2+1-31D)Q(f)`. The zero-order hybrid pair explicitly gives `||f||_2^4<=Q(f)`. For `D>=1`, the final numerical check is `162*(2^(-94D^2)+2^(1-31D))<1`, proving A7. Degree zero is the separate equality base case.

Current actual W6-related Lean declarations: `complex_carrier_parseval`, `actualW6Derivative_energy_parseval`, carrier coefficient/fiber sum and Cauchy bounds, `actualW6Derivative_fourierEnergy_fiber_partition`, `w6_actual_predecessor_frequency_fiber_card`, and `actualW6Derivative_weighted_fourth_moment_le_67_63` / `..._le_two`. The last pair bounds a weighted sum of squared carrier means for the actual W6 derivative. This audit did not verify a theorem with the manuscript's W6 interface applied to every actual hybrid derivative input in A11, including exact normalization, average over `T`, and the unweighted full hybrid `Q(f)` endpoint. That bridge must be stated and checked; nearby theorem names do not discharge it.

## Corrected unresolved implication ledger

1. T1 on actual subspaces: `C=Y(B) intersect A`; keep `X:H/B -> A/C` separate from `R=q_CY|H:H->V/C`. Formalize both selector directions, unique reconstruction, and the pointwise complex derivative sum with exact common phase/frequency.
2. T2 on arbitrary actual `S,T`: formalize both selector directions, rank-loss equality consequences, uniqueness of `C,H`, equal phase, and grouped sum without assuming distinct frequencies.
3. Simultaneous degree induction over all finite spaces: exact support preservation and `D-t<D`; internal `D=0` Fourier inversion and zero-order equality.
4. A8: induction -> T2 -> A1; graph/Holder cost `<=2^(3Dk)<=2^(6Dk)`; correct mixed order `s+k+u+v<=D`, without asserting ordinary order `s+2k+u+v<=D`.
5. A9: prove the actual graph-data bijection/count, including inverse, rank preservation, and the final-term condition `a+b+k<=D`; separately retain initial mixed condition `i+j+k<=D`.
6. A10/A11: reindex all actual terms with multiplicities; keep common cutoff `D`; bridge exact W6 normalization and the all-hybrid unweighted `Q(f)`; preserve coefficient factors and zero-order term.
7. Endpoint: verify `162*(2^(-94D^2)+2^(1-31D))<1` for `D>=1`, with the degree-zero equality handled separately.

## Evidence boundary

The corrected note is an argument and interface audit for independent sufficiency review only. It makes no statement that A7 is proved, accepted by Lean, or implementation-ready. The full-scope DR6 endpoint and F2 incidence theorem remain distinct results. No implementation/module/compiler/Git action was taken. No helper count is claimed as progress.