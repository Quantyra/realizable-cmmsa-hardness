# Realizable Nearlinear-Gap Hardness for Small Monotone Formulas

Quantyra Research | 12 September 2026 | Version 0.1.0

## Abstract

For every sufficiently large fixed leaf bound L, we prove randomized
polynomial-time many-one NP-hardness of realizable Collection Minimum
Monotone Satisfying Assignment with weight gap L^(1-o(1)) and NO
satisfaction threshold o(1). The corresponding bounded-advice learning
statement follows through Hirahara--Nanashima's transfer. This establishes
the epsilon=0 strengthening asked in Section 7 of their June 23, 2026
revision. We combine their star-projection compilation with
Minzer--Zheng's Grassmann PCP machinery, an altered repetition parameter
order, explicit advice-posterior and zoom-out estimates, a maximal-extension
threshold ladder, and finite-list completeness repair. Every leaf/advice
bound is fixed independently of input length; the polynomial exponent may
depend on it. The contribution is the nearlinear exponent in the realizable
regime, with earlier realizable hardness explicitly credited below.

## Problems, conventions, and results

A monotone formula is an AND/OR formula with positive variable leaves;
repeated occurrences count separately. F[L] denotes formulas with at most
L leaves. Constants arising from empty branches may be simplified away.
For x in {0,1}^N and positive rational weights w_i with sum_i w_i=1, write
w(x)=sum_{i:x_i=1} w_i. An instance of
Gap^(epsilon,gamma)_sigma F[L]-CMMSA is an indexed nonempty explicit list
F_1,...,F_M, those weights, and a rational budget 0<s<=1. The promises are:

* YES: some x with w(x)<=s satisfies at least a 1-epsilon fraction of the list.
* NO: every x with w(x)<=sigma s satisfies strictly less than a gamma fraction.

Indices count with multiplicity. Weights and budgets have polynomial bit
encodings and inverse-polynomial lower bounds in the number of variables.
This is the normalized-weight restriction of HN Definitions 1.7 and 4.1.
The distributional version DMMSA specifies the formula distribution by a
sampling circuit. Our final output is an explicit power-of-two list, also
represented by its exact uniform sampler. Realizable means epsilon=0.

A randomized polynomial-time many-one reduction maps each input to one
output instance, and for each input satisfies the appropriate YES or NO
promise with probability at least 2/3. All randomness and output lengths
are polynomially bounded. The theorem asserts one such uniform reduction
on input instances for each fixed L, with no common polynomial exponent
asserted across L. Limits as L grows compare this family of separately
fixed reductions.

**Theorem 1 (realizable CMMSA).** There are functions sigma_L in the
positive integers and gamma_L in (0,1), with

    log(sigma_L)/log L -> 1,    gamma_L -> 0,

such that, for every sufficiently large fixed integer L,
Gap^(0,gamma_L)_(sigma_L) F[L]-CMMSA is NP-hard under randomized
polynomial-time many-one reductions. The output weights and budget can
be required to share a polynomial-magnitude common denominator.

For completeness we specify the learning model. Fix the universal machine
U used by HN. In their Definition 3.11, a distribution on {0,1}^n has advice
complexity at most a if a function alpha mapping random strings of length
2^(2n) to strings of length at most a makes U(alpha(r);r,n) halt on every
r, with failure-output probability at most 1/4 and conditional output
statistical distance at most 2^(-2n) from the distribution. The advice can
depend on r and need not be computable. This parameter is not the length
of a conventional fixed sampler description. For labeled examples use
the total encoded sample length in this definition.

Gap^(epsilon,gamma)_sigma Learn[a] takes unary length and program-budget
parameters 1^n,1^s and an example oracle E on {0,1}^n times {0,1}, promised
to have sampling advice complexity at most a. Its YES case has a program
of description length at most s running in linear time and agreeing with
the labels with probability at least 1-epsilon. Its NO case bounds the
agreement of every program of description length at most sigma s by
1/2+gamma/2. The NO assertion does not impose an efficient running-time
restriction on those programs. We use HN's machine and encoding convention;
the universal overhead below is the associated constant c_U. Our reduction
outputs an explicit sampling circuit, so the hardness also holds with that
circuit supplied in place of only oracle access.

**Corollary 2 (realizable learning).** For every sufficiently large fixed
integer advice cap a, put

    L=a-2 ceil(log2(a+1))-c_U,
    sigma^learn_a=floor(0.49 sigma_L),    gamma^learn_a=5 gamma_L.

Then Gap^(0,gamma^learn_a)_(sigma^learn_a) Learn[a] is NP-hard under
randomized polynomial-time many-one reductions. For large a the parameters
are in their required domains, sigma^learn_a=a^(1-o(1)), and
gamma^learn_a=o(1). In YES instances the linear-time program has agreement
exactly one; in NO instances all programs within the expanded description
budget have agreement at most 1/2+gamma^learn_a/2.

These are approximation-hardness results under randomized reductions.
They give no complexity-class separation, one-way-function construction,
linear-factor hardness, or growing-parameter reduction. No assertion about
general improper PAC learning or circuit size is made.

## Relation to previous work

HN revision 1 proves the nearlinear exponent with vanishing nonzero YES
error and asks its realizable strengthening separately from its
superconstant-parameter question. Hirahara's FOCS 2022 work already proves
realizable learning hardness; HN explicitly records the corresponding
realizable CMMSA factor L^alpha for a constant alpha>0, with threshold
1/L^alpha. The advance here is the nearlinear exponent, not the first
realizable hardness theorem. The source contracts are the corrected June
23, 2026 revision, not the withdrawn superconstant regime of an earlier
version. [HN, Definitions 1.2/1.7, Theorems 1.3/1.8, Section 7;
Hir22](SOURCES.md).

The MZ higher-query construction gives soundness nearly R^(-m) with m+1
queries but its displayed main theorem chooses the alphabet after both
positive errors. Our proof changes the construction's parameter order;
substituting an inverse-alphabet completeness error into that main theorem
alone would be circular. MZ24's two-query result, even granting its
alphabet-before-completeness abstract formulation, does not provide this
higher-arity contract: independent two-query repetition spends two queries
per repetition. Likewise a perfect-completeness dictatorship test is not
by itself this unconditional star-projection PCP. The targeted literature
assessment found no exact subsumer, but does not certify novelty or priority.
[MZ, MZ24, BKM](SOURCES.md).

Slack variables, AND products, concentration, weight rounding, secret
sharing, and the star compilation are established techniques. The new
argument is their quantitative composition with the modified repetition,
actual advice posterior, conditional rank/zoom-out control, and descending
threshold ladder. We import the local Grassmann theorems and the outer
hardness machinery rather than reprove them. The STOC 2026 full text of MZ
was not accessible in the assessment; claims about its numerical details
are confined to the accessible arXiv v1, also linked by a coauthor.

## Notation and imported contracts

All vector spaces are over GF(2). Grass(E,d) is the set of d-dimensional
linear subspaces of E, with uniform distribution unless stated otherwise.
[n choose a]_2 is the Gaussian binomial coefficient counting a-subspaces
of an n-space. SD is total variation distance (one half the L1 distance).
Zoom[Q,W] is the uniform d-subspace L with Q subset L subset W, where
d=2h. The symbol L for a subspace is local to the Grassmann argument;
the scalar L in Theorem 1 always denotes the final leaf bound. Similarly,
a denotes advice dimension in that argument and the final advice cap only
in Corollary 2. The final asymptotics use base-two log, and ln is natural log.
The parameters m,h,rho,J are leaf-query count, inner dimension parameter,
rational decoding slack, and repetition count. Set r=10m/rho, choosing rational rho with this value integral. Thus r is
a fixed integer bound on advice dimensions and zoom-out codimensions;
the local decoder gives a+c<=r.

The proof uses the following established inputs at their stated parameter
ranges. Precise public versions and bibliographic links are in
[SOURCES.md](SOURCES.md). The contracts are explicit mathematical imports;
none is a locally formalized theorem.

1. **Outer hardness and game (MZ Theorem 3.1, Section 3.2, Claim 3.2).**
   There is an absolute NO value s_0<1 for 3-Lin, while its fixed positive
   YES error may be arbitrarily small. Use the bounded-occurrence form
   with no pair of variables in more than one equation. In the smooth
   repeated game choose J equations independently; in each triple keep
   all coordinates with probability 1-beta, otherwise a uniform single
   coordinate. Both provers receive the same r random vectors on the
   retained coordinates, extended by zero to the first question. They
   answer assignments; acceptance requires agreement on retained variables
   and satisfaction of the J equations. With fixed NO gap eta=1-s_0,
   its value is at most 2^(-Omega(eta^2 2^(-r) beta J)); its honest failure
   is at most J times the outer YES error. In particular the soundness
   constant does not depend on that later YES error.
2. **Star construction and transport (MZ Section 3.3, Lemmas 3.3--3.4).**
   Keep tuples U of J disjoint equations with no cross-equation pair of
   variables occurring together in any equation. View U as a 3J-space and
   let H_U be the span of its equation indicator vectors, of dimension J.
   Labels at L+H_U, with dim L=2h and L transverse to H_U, are linear
   functions satisfying the equation right-hand sides on H_U; there are
   R=2^(2h) labels. Center labels are linear functions on a transverse
   2(1-rho)h-subspace K. Two leaf vertices are equivalent when
   L+H_U+H_U'=L'+H_U+H_U'. The imported lemmas give an equivalence relation
   and unique side-condition-preserving label transport. The test chooses
   U uniformly, K uniformly transverse, m independent transverse L_i
   containing K, then a uniform representative from each leaf's equivalence
   class. It transports each queried label back and tests restriction to K
   against the center label. This is a weighted star-projection (m+1)-CSP,
   with alphabets at most R; all choices are finite and enumerable in
   N_outer^(O_m(J)). Clique-consistency selection and the collision estimate
   from Section 5.4.1 preserve the value, up to a vanishing Gaussian-binomial
   collision loss bounded above by our explicit estimates.
3. **Local decoder (MZ Theorem 4.2).** For fixed small rho>0 and sufficiently
   large integral h with integral test dimensions, transverse tables obeying
   the above side conditions and test density at least
   2^(-2(1-1000rho)hm) have dimensions a,c with a+c<=10m/rho such that at
   least 2^(-6h^2) of the uniform a-subspaces Q admit W containing Q+H_U,
   of codimension c, and a linear g on W respecting H_U, with agreement
   at least C=2^(-2(1-1000rho^2)h)/5 on the conditioned Grassmann space.
   This is the source construction's scoped contract. For the changed ambient
   parameter we derive a robust application with input density at least
   eight times this threshold below, rather than importing an all-J theorem.
   Transversality losses are charged explicitly below.
4. **Maximal-pair counting (MZ Definition 5.4; MZ24 revision 1 Theorem 5.26).**
   For a total table of linear functions on Grass(V,2h), a pair (W,g) is
   (B,1/5)-maximal relative to Q if it agrees with the table on at least B
   of Zoom[Q,W], and no proper extension W' with a linear extension of g
   agrees on at least B/5 of Zoom[Q,W']. Specialize MZ24 with field GF(2)
   and its delta=rho/m, fixing its subsidiary constants as in Lemma 5.24
   before taking h large. For dim V>=2^h, dim Q<=10m/rho, codim W<=10m/rho,
   and B>=2^(-2(1-(rho/m)^3)h), the number of these maximal pairs is at most
   B^(-2) 2^(O_(m,rho)(h)). We use the stronger cutoff
   B>=2^(-2(1-rho^3)h), which implies this one. Thus we require no
   advice range proportional to J from the broader printed MZ Theorem 5.5.
   Counting does not assert extension at a single lowered threshold; the
   threshold ladder below supplies that step.
5. **Covering (KMS Definition 4.5, Lemmas 4.6--4.7).** For the independent
   triple-deletion sampler with 2^d beta<=1/8, basic d-subspace distance
   is at most beta sqrt(J) 2^(d+4). For advice dimension a<d, except for
   at most sqrt(beta) J^(1/4) of uniform a-subspaces Q, the distance after
   conditioning on containing Q is at most sqrt(beta) J^(1/4) 2^(d+5).
   The condition is on the joint sampler, changing the distribution of V.
   These covering lemmas are unconditional results proved in KMS Section 8;
   they do not require its historical combinatorial hypothesis or UGC.
6. **Compilation (HN Lemma 4.6).** For a star constraint
   e=(y;x_1,...,x_m), let pi_(e,i) map its leaf alphabet to the center.
   Its acceptance is pi_(e,i)(label(x_i))=label(y) for every i. Give a vertex
   u occurrence weight lambda(u)=E_e[1[y=u]+sum_i 1[x_i=u]]/(m+1), discarding
   zero-occurrence vertices. Set Lambda=sum_u lambda(u)|Sigma_u|,
   w(z_(u,b))=lambda(u)/Lambda, and s=1/Lambda. If X_e is the set of distinct
   leaf vertices, let P_(e,x,b) contain labels at x whose projections at
   every occurrence of x equal b. Output the monotone formula

       F_e = OR_(b in Sigma_y) [z_(y,b) AND
                   AND_(x in X_e) (OR_(a in P_(e,x,b)) z_(x,a))].

   Empty ORs are false. Repeated leaf consistency is imposed in P, not
   discarded. The formula has at most (m+1)R leaves. Value at least 1-tau
   gives a weight-s assignment satisfying at least 1-tau of these formulas.
   CSP value at most zeta implies every assignment of weight at most
   (1/8)(5/8)^(1/(m+1)) zeta^(-1/(m+1)) s satisfies at most 3/4 of them.
7. **Secret sharing and learning (HN Theorem 3.5 and Lemma 5.1).** Formula
   leaf bound L supplies a polynomial-time secret-sharing scheme with
   total share length at most L. For a circuit-sampled distribution of
   such formulas, positive inverse-polynomial rational weights and budget,
   and parameters epsilon in [0,1], gamma in (0,1], sigma>=1, the randomized
   transfer preserves epsilon, changes gamma to 5gamma and sigma to
   0.49sigma, and gives advice at most L+2ceil(log2(L+1))+c_U. Its YES
   guarantee holds for every transfer random string; its NO guarantee fails
   with only negligible probability. A sufficiently large polynomial length
   parameter must make all weighted string lengths integral and satisfy
   the description/soundness bounds. Our common-denominator step supplies
   this requirement. Integer gap factors are obtained by rounding down.

We now prove the parameter extension and the remaining composition in full.
The local input theorems above retain their usual external-proof status.

## Explicit-list exception lemma

Input: M>=1 monotone formulas F_1,...,F_M on N variables, each with at most
L leaves; positive rational weights w_i summing to one; positive rational
budget s<=1; integer sigma>=8; rational 0<Gamma<1/2; and rational epsilon
with epsilon>=0 and epsilon sigma <= Gamma/2. The promises are:

* YES: some assignment of weight at most s satisfies at least 1-epsilon
  of the list, counting indices with multiplicity.
* NO: every assignment of weight at most sigma s satisfies strictly less
  than Gamma of the list.

Set lambda=sigma s/Gamma. Introduce M fresh variables e_j and replace
F_j by F_j OR e_j. Give original variables raw weights w_i and every e_j
raw weight lambda/M; divide every weight by 1+lambda. Set

    t = (s + lambda epsilon)/(1+lambda),
    sigma_new = floor(sigma/4), Gamma_new = 2 Gamma.

In the YES case, take an original witness and enable exactly the exception
bits for its failed list indices. Its raw weight is at most s+lambda epsilon,
and it satisfies every augmented formula. No witness or failed-index set
is needed to compute the reduction: these choices establish existence.

In the NO case, any augmented assignment of normalized weight at most
sigma_new t has raw weight at most

    floor(sigma/4)(s+lambda epsilon) <= 3 sigma s/8.

Its original-variable part therefore satisfies less than Gamma of the
original list. Its enabled exception bits occupy at most

    (3 sigma s/8)/lambda = 3 Gamma/8

of list indices. The augmented acceptance fraction is strictly less than
11 Gamma/8, hence strictly less than 2 Gamma. This proves the claimed
perfect-completeness gap reduction. Normalization cancels in both budget
comparisons, and t<=1 because s<=1 and epsilon<=1.

The output has N+M variables, M formulas and at most L+1 leaves per formula.
Construction copies the list, adds M OR gates, and performs rational
arithmetic on input rationals. It is polynomial in the actual input and
output bit lengths. For fixed sigma,Gamma, inverse-polynomial lower bounds
on w_i and s imply the same for the normalized weights, t, and lambda/M.
No SAT, optimum, or counting oracle is used. Applying this directly to an
exponential implicit distribution would be invalid; sampling precedes it.

## Why the repetition parameters are changed

The alphabet of the MZ star construction is R=2^(2h). Its displayed
choice J=2^(100h^2), beta=loglog(J)/J has beta J=O(log h), so its
outer-game estimate alone does not give an exponent proportional to h^2.
We use J=2^(2^(A h^2)), beta=A h^2/J. This observation concerns only
arXiv 2510.23991v1; it is not a disproof of its main theorem or a claim
about the uninspected STOC 2026 text. The argument below proves the
needed parameter order using the local imported contracts.

## Parameter extension: posterior and zoom-out argument

This section supplies the parameter modification rather than treating an
inverse-alphabet completeness error as part of a black-box theorem.
All logarithms here are base two (ln denotes the natural logarithm). Fix an integer m>=2 and a positive rational rho<=1/4000.
Use the local decoding and maximal-pair counting contracts stated above
(MZ Theorem 4.2 and the narrower MZ24 Theorem 5.26 specialization). Their parameters r and the constants
in their bounds depend on m,rho. The following lemmas justify the
changed ambient application with an explicit constant input margin.
Choose h sufficiently large relative to these fixed parameters and a
multiple of b_m, the denominator of the selected rational rho. Then
2(1-rho)h and all test dimensions are integers. All
subspaces below are over GF(2), U consists of J disjoint triples, and
dim(U)=3J. The side-condition space H_U has dimension J.

```latex
\begin{lemma}[Exact complement identity for star queries]\label{lem:complement}
Let $U=H\oplus Z$, with $\dim H=J$, $\dim Z=2J$, and $t\le d\le2J$.
Draw a uniform $t$-space $K$ transverse to $H$, then independent uniform
transverse $d$-spaces $L_i\supseteq K$, for $1\le i\le m$.
The law of $(K,H+L_1,\ldots,H+L_m)$ equals the law obtained by drawing
a uniform complement $A$ of $H$, a uniform $t$-space $K\subseteq A$,
and independent uniform $d$-spaces $L_i'\subseteq A$ containing $K$,
and outputting $(K,H+L_1',\ldots,H+L_m')$.
\end{lemma}
\begin{proof}
Fix $K$. Projection to $Z$ expresses it as the graph of a map on a
$t$-space $\overline K$. Each possible $D=H+L$ corresponds to a
$d$-space of $Z$ containing $\overline K$. Its transverse lifts containing
$K$ are exactly the $2^{J(d-t)}$ extensions of that graph map.
Consequently the $D_i$ are independent and uniform among these possible
spaces. Independently choose a uniform complement $A$ containing $K$.
The map $D_i\mapsto A\cap D_i$ is a bijection to the $d$-spaces of $A$
containing $K$, and $H+(A\cap D_i)=D_i$.
There are $2^{J(2J-t)}$ complements containing each transverse $K$,
while every complement contains the same Gaussian-binomial number of
$t$-spaces. Thus the uniform incidence law of $(K,A)$ can be sampled
in either order, proving the assertion.

The actual leaf table is indexed by $D_i=H+L_i$ and its transported
label is restricted to $K$. The acceptance event is therefore preserved
exactly. Random clique representatives can be coupled at identical
$D_i$, with identical transport; alternatively use the already selected
clique-consistent table. No condition on intersections among projected
leaf increments is needed. This is not an identity of the unobserved
raw tuples $(K,L_1,\ldots,L_m)$.
\end{proof}

\begin{lemma}[Finite matrix-lift pseudorandomness]\label{lem:matrix-lift}
Let $E=\mathbb F_2^n$, $D=\mathbb F_2^d$, $n\ge d$, and
$0\le r<d$. Suppose $g:\operatorname{Grass}(E,d)\to\{0,1\}$ has
uniform density at most $e\ge0$ in every nonempty zoom
$\{L:Q\subseteq L\subseteq W,\ \dim L=d\}$ with
$\dim Q+\operatorname{codim}_E W=r$.
Define $G(M)=g(\operatorname{im}M)$ for rank-$d$ maps $M:D\to E$,
and $G(M)=0$ for deficient maps. Then $G$ is basis invariant and
its expectation is at most $2e$ on every nonempty affine restriction
\[
 \{M:MU=V,\ XM=Y\}
\]
whose nominal budget is $a_0+b_0=r$, where $U$ has $a_0$ columns and
$X$ has $b_0$ rows. Neither family of constraints need be independent.
This nominal budget counts vector equations, not ordinary affine-space
codimension. Since $G$ is Boolean, the conclusion is the restricted
squared-$L_2$ bound in matrix $(r,2e)$-pseudorandomness.
\end{lemma}
\begin{proof}
This reconstructs the finite bridge of MZ Lemma~4.5 and MZ24
Lemmas~A.17--A.18, with the strict budget and all affine fibres explicit.
For invertible $B:D\to D$, $\operatorname{im}(MB)=\operatorname{im}M$
and ranks agree, proving basis invariance.

Reduce columns of $(U,V)$ by invertible operations. A dependent column
relation violated by $V$ makes the restriction empty; otherwise delete
redundant equations and retain $a=\operatorname{rank}U\le a_0$
independent domain vectors. If their prescribed images are dependent,
every satisfying $M$ has a nonzero kernel and $G=0$.
In the remaining case, change domain coordinates to make these the
first $a$ columns, denoted $V$, with independent images. Row operations
on $(X,Y)$ similarly delete consistent redundancies (an inconsistent
zero row is the empty case). Let $b=\operatorname{rank}X\le b_0$.
Compatibility on the fixed columns is necessary; the remaining
uniform restriction has the form
\[
 M=[V,N],\qquad XN=B,\qquad k=d-a,\qquad a+b\le r<d.
\]
All operations are bijections or deletion of redundant equations;
they preserve finite uniform conditional laws and lift values.
Empty restrictions have no conditional law and require no assertion.
In particular $b<k$.

Reduce $(X,B)$ together so $B$ has $c=\operatorname{rank}B$
independent rows $B_1$ followed by zero rows; write
$X=(X_1;X_0)$ accordingly. The $b$ rows of $X$ are still independent.
For $H_0=\ker X_0$, the map $X_1:H_0\to\mathbb F_2^c$ is onto:
the combined map $(X_1,X_0)$ is onto, so any target $(y,0)$ lifts.
For uniform free columns $N\in H_0^k$, the target $X_1N$ is therefore
uniform among all $c$-by-$k$ matrices, with equal fibres. The probability
that it has full row rank is
\[
 \pi(c,k)=\prod_{i=0}^{c-1}(1-2^{i-k})
 \ge1-2^{-k}(2^c-1)>\tfrac12,
\]
using $c\le b<k$; the empty product at $c=0$ equals one.

The right action of $\operatorname{GL}(k,2)$ is transitive on
full-row-rank $c$-by-$k$ targets. The bijection $N\mapsto NB_0$
for such an invertible $B_0$ preserves $X_0N=0$ and the value
$G([V,N])$, by right multiplication with $\operatorname{diag}(I_a,B_0)$.
Thus its conditional expectation is identical at every full-rank
target and equals the expectation conditioned on full target rank.
Nonnegativity gives
\[
 \mathbb E[G([V,N])\mid X_1N=B_1,\ X_0N=0]
 \le\pi(c,k)^{-1}\mathbb E[G([V,N])\mid X_0N=0]
 \le2\mathbb E_{\mathrm{hom}}G.
\]
This is the sole factor two; it concerns the small target matrix,
not a large-$n$ rank approximation.

For the homogeneous experiment put $Q=\operatorname{span}V$,
$H=\ker X_0$, $W=Q+H$, and $z=\dim(Q\cap H)$.
This is ordinary subspace sum; no disjointness is assumed.
Its budget satisfies $\dim Q+\operatorname{codim}W\le a+b-c\le r$.
If no $d$-space lies between $Q$ and $W$, the lift is identically zero.
Otherwise, for each such $L$, the map $L\cap H\to L/Q$ is onto
with kernel $Q\cap H$: writing a vector of $L$ as $q+h$ puts
$h$ in $L\cap H$. The quotient has dimension $k$.
The free columns yield rank $d$ and image $L$ exactly when their
quotient images form an ordered basis. There are exactly
\[
 |\operatorname{GL}(k,2)|\,2^{zk}
\]
choices, independent of $L$. Conditioning the homogeneous columns
on full rank therefore gives the uniform zoom law, and zero on the
complement gives
\[
 \mathbb E_{\mathrm{hom}}G
 =\Pr_{\mathrm{hom}}[\operatorname{rank}[V,N]=d]
       \mathbb E_{L\in\operatorname{Zoom}[Q,W]}g(L)
 \le \mathbb E_{L\in\operatorname{Zoom}[Q,W]}g(L).
\]
No division by the full-rank probability is made.

Finally put $w=\operatorname{codim}W$ and $a'=r-w$.
Then $\dim Q\le a'<d$. Average first over uniform $a'$-spaces
$Q'$ with $Q\subseteq Q'\subseteq W$, then over uniform $d$-spaces
between $Q'$ and $W$. Both incidence fibre counts are constant:
every $Q'$ has the same number of extensions, and every $L$ in the
original zoom has the same number of intermediate $Q'$.
The marginal $L$ is consequently uniform on the original zoom.
Every refined zoom has exact budget $r$, so its density is at most
$e$; averaging proves that bound for the smaller budget as well.
Combining the homogeneous estimate with the affine-target estimate
proves $\mathbb E G\le2e$, including all nonempty redundant or
dependent cases considered above.
\end{proof}

\begin{lemma}[Finite-character spectral bound]\label{lem:finite-spectral}
Let $0\le s\le d$, $c=d-s$, and use uniform averages on finite binary
matrix spaces, including deficient matrices. Define
\[
 \begin{aligned}
 (\mathcal TF)(X)&=\mathbb E_{B\in\mathbb F_2^{n\times s}}F([X,B]),
       &&X\in\mathbb F_2^{n\times c},\\
 (\mathcal GH)(M)&=\mathbb E_{R\in\mathbb F_2^{d\times c},\,
                         \operatorname{rank}R=c}H(MR),\\
 (\Phi F)(M)&=\mathbb E_{B\in\mathbb F_2^{n\times s},\,
                    C\in\mathbb F_2^{s\times d},\,
                    \operatorname{rank}C=s}F(M+BC).
 \end{aligned}
\]
In the last line $B,C$ are independent, $B$ is unrestricted, and only
$C$ is conditioned on rank. Suppose $F(MA)=F(M)$ for every
$A\in\operatorname{GL}(d,2)$ and every $M$. Let $F_i$ be its Fourier
projection onto characters indexed by rank-$i$ matrices. Then the
$\mathcal TF_i$ are mutually orthogonal, and
\[
 \|\mathcal TF_i\|_2^2=\lambda_i\|F_i\|_2^2,
 \qquad 0\le\lambda_i\le2^{-is}.
\]
In particular the weaker bound used below is valid:
\[
 \|\mathcal TF_i\|_2^2
 \le\bigl(2^{-i(s-1)}+3\cdot2^{i-n}\bigr)\|F_i\|_2^2.
\]
\end{lemma}
\begin{proof}
We reconstruct the finite-character calculation behind MZ Lemma~4.7
and MZ24 Lemmas~A.10--A.13 for their actual sampling laws.
Use $\langle F,H\rangle=\mathbb E[F\overline H]$ and let $J_0$ be
the inclusion of the first $c$ coordinates. The ordinary adjoint of
$\mathcal T$ is fixed-coordinate pullback, but for basis-invariant $F$
we may average $M\mapsto MA$ over uniform invertible $A$ to obtain
\[
 \langle\mathcal TF,H\rangle
 =\mathbb E_M F(M)\overline{H(MJ_0)}
 =\mathbb E_{N,A}F(N)\overline{H(NA^{-1}J_0)}
 =\langle F,\mathcal GH\rangle.
\]
Each full-column-rank injection $A^{-1}J_0$ has the same number of
invertible completions, so its law is the specified uniform law.
No invariance of $H$ is required; the identity is not asserted for
arbitrary first arguments.

To compute the composition, complete a uniform injection $R$ uniformly
to $A=[R,A_2]\in\operatorname{GL}(d,2)$. At fixed $M,A$ the appended
uniform matrix has the law $MA_2+W$ with $W$ unrestricted. Therefore
\[
 (\mathcal G\mathcal TF)(M)
 =\mathbb E_{A,W}F(MA+[0,W])
 =\mathbb E_{A,W}F(M+[0,W]A^{-1})
 =\mathbb E_{W,C}F(M+WC)=(\Phi F)(M).
\]
Basis invariance justifies the second equality. The last $s$ rows
$C$ of $A^{-1}$ are uniform full row rank by constant completion
fibres, and $W$ remains independent of $C$. These statements include
empty matrices at $s=0$ or $c=0$ and deficient $M$.

For $S\in\mathbb F_2^{n\times d}$ put
$\chi_S(M)=(-1)^{\sum_{u,v}S_{uv}M_{uv}}$.
Finite character cancellation makes these an orthonormal basis.
Translation gives $\Phi\chi_S=\lambda_S\chi_S$, where
$\lambda_S=\mathbb E_{B,C}\chi_S(BC)$.
At fixed $C$, the exponent pairs $B$ with $SC^{\mathsf T}$.
Averaging the unrestricted entries of $B$ cancels to zero unless
$SC^{\mathsf T}=0$, when every term is one. Consequently
\[
 \lambda_S=\Pr_C[SC^{\mathsf T}=0].
\]
If $\operatorname{rank}S=i$, the rows of $C$ must form an ordered
independent $s$-tuple in the $(d-i)$-dimensional kernel of $S$.
Counting these tuples yields
\[
 \lambda_i=\begin{cases}
 0,&s>d-i,\\
 \displaystyle\prod_{j=0}^{s-1}
       \frac{2^{d-i}-2^j}{2^d-2^j},&s\le d-i.
 \end{cases}
\]
The empty product is one. Every nonnegative factor is at most $2^{-i}$,
so $0\le\lambda_i\le2^{-is}$. This proves positivity directly and
shows that the eigenvalue depends only on rank, not orientation or $n$.

The identity $\chi_S(MA)=\chi_{SA^{\mathsf T}}(M)$ permutes character
indices without changing rank. Thus every rank projection $F_i$ of a
basis-invariant $F$ is itself basis invariant, and
$\Phi F_i=\lambda_iF_i$; individual characters need not be invariant.
The restricted adjoint and composition identities now give
\[
 \langle\mathcal TF_i,\mathcal TF_j\rangle
 =\langle F_i,\Phi F_j\rangle
 =\lambda_j\langle F_i,F_j\rangle.
\]
Orthogonality and the squared-norm formula follow. The unsquared
contraction would be $\sqrt{\lambda_i}$, not $\lambda_i$.
Finally $2^{-is}\le2^{-i(s-1)}+3\cdot2^{i-n}$ gives the stated
weaker estimate. We retain that weaker form and the conservative
ambient conditions in the inverse proof; no constants are reoptimized.
\end{proof}

\begin{lemma}[Inverse agreement with explicit ambient bounds]\label{lem:inverse-explicit}
Fix $m\ge2$, $0<\rho\le1/4000$, and integral $r=10m/\rho$.
Let $h$ be sufficiently large with integral dimensions
$t_0=2(1-\rho)h$, $s_0=2\rho h$, $d=2h$; write
\[
 S=2^{-2(1-1000\rho)hm},\qquad
 e=2^{-2(1-1000\rho^2)h},\qquad b=s_0-1.
\]
For tables of linear functions on the $d$-spaces and $t_0$-spaces
of an $n$-space, suppose the actual test (uniform center and independent
uniform containing leaves) has density $\epsilon\ge S$.
Under the ambient lower bounds below, some nonempty
$\operatorname{Zoom}[Q,W]$ with
$\dim Q+\operatorname{codim}W=r$ admits a linear function with
agreement greater than $e$ with the leaf table.
The constants and the lower cutoffs on $h$ depend only on $m,\rho$.
\end{lemma}
\begin{proof}
Lemma~\ref{lem:matrix-lift} supplies the matrix lift of an
$(r,e)$-pseudorandom Grassmann indicator as an $(r,2e)$-pseudorandom
basis-invariant indicator. The strict budget $r<d=2h$ holds in the
regime $h\ge r>0$ below, and the ambient bounds imply $n\ge d$.
Theorem~\ref{thm:binary-hc} in Appendix~\ref{app:binary-hc} proves
the required binary specialization of MZ~\cite{MZ}, Theorem~4.6:
it bounds the level-$i$ norm at every dyadic $p\ge4$ by
$2^{500i^2p}(2e)^{(p-2)/p}$ for $i\le r$.
The appendix derives this inequality from finite Fourier arguments,
with the nominal matrix-restriction interface used here.
Lemma~\ref{lem:finite-spectral}, with $s=s_0=2\rho h$, supplies
cross-level orthogonality and the unchanged spectral bound
\[
 \|\mathcal T F^{=i}\|_2^2
 \le \bigl(2^{-i(2\rho h-1)}+3\cdot2^{i-n}\bigr)
       \|F^{=i}\|_2^2.
\]
The matrix and spectral bridges are proved above; the analytic inequality is proved in the appendix.
We reconstruct the intervening moment, selection and exponent steps
rather than invoke the printed inverse proof without these bounds.

Require $h\ge r$, $e\le1/2$, and
\[
 (2h+2\rho mh)2^{2h-n}\le\tfrac12,\qquad
 b\ge1,\qquad n\ge2h+rb+\log_2 6.
\]
The first condition bounds the probability of any column-rank failure
in the common-center matrix sampler. Conditioned on full rank, the
subspace law is the actual uniform star law; the matrix indicators
vanish otherwise. Thus the star density for sets is at most twice
the corresponding matrix expectation.
For an $(r,e)$-pseudorandom leaf set with lift $F$, decompose
$\mathcal T F=L+H_{\mathrm{high}}$ into levels at most $r$ and above $r$.
Orthogonality and the spectral input give
\[
 \|H_{\mathrm{high}}\|_2^2
 \le2^{-(r+1)b}+3\cdot2^{2h-n}\le2^{-rb}.
\]
Take $\eta=2^{-(2/3)r\rho h}$. Markov's inequality gives
$\Pr[|H_{\mathrm{high}}|>\eta]\le2^r2^{-(2/3)r\rho h}$.
On its complement use
$|L+H_{\mathrm{high}}|^m\le2^{m-1}(|L|^m+\eta^m)$;
on the exceptional event use $0\le\mathcal TF\le1$.

Choose a power of two
$T\ge\max(4,4(m+3)/(m\rho))$, and let $P$ be the least power of two
at least $mT$. These depend only on $m,\rho$.
For the lifted center indicator $G$, whose expectation is at most its
Grassmann density $\beta$, H\"older contributes $\beta^{1-1/T}$.
Probability-space norm monotonicity, contraction of $\mathcal T$,
and the dyadic norm input at $P$ imply
\[
 \|L\|_{mT}^m
 \le(r+1)^m2^{500mr^2P}(2e)^{m-2m/P}
 \le(r+1)^m2^{500mr^2P+m}e^{m-2/T}.
\]
The last inequality uses $P\ge mT$ and $2e\le1$.
Combining the splitting and rank factors, the actual matching-star
density $X$ for these two sets satisfies
\[
 X\le K_{\mathrm{inv}}\beta^{1-1/T}e^{m-2/T}
       +D_{\mathrm{inv}}2^{-(20/3)mh},
\]
where the deliberately conservative constants are
\[
 K_{\mathrm{inv}}=2^{2m}(r+1)^m2^{500mr^2P},\qquad
 D_{\mathrm{inv}}=2^m+2^{r+1}.
\]
In particular we do not use the stronger printed high-degree error
or a norm theorem at a possibly nondyadic exponent $mT$.

For the selection step, a good tuple has its $m$ quotient increments
$L_i/R$ in joint direct sum, not merely pairwise trivial intersection.
Its total span has dimension $t_0+ms_0$, so labels agreeing on the
center glue to a linear function on that span. Expose ordered leaf
bases modulo the center. At increment index $j$, the previously
exposed span has at most $2^{t_0+j}$ vectors and the allowed sampling
denominator is at least $2^{n-1}$ when $n\ge d+1$. A union bound gives
\[
 q=\Pr[\text{not jointly direct}]<2^{t_0+ms_0+1-n}\le S/2
 \quad\text{if } n\ge t_0+ms_0+2+\log_2(1/S).
\]
Thus good accepting tuples have mass at least $\epsilon/2$.
This joint-span condition is needed for gluing arbitrary labels in the
inverse argument; it is not a loss in Lemma~\ref{lem:complement}'s
exact quotient-query identity.

Choose a uniform global linear $f$. Let $X_f$ be the unrestricted
star density for which all leaf and center labels match $f$, and let
$\beta_f$ be its matching-center density. Then
\[
 \mathbb E X_f\ge(\epsilon/2)2^{-(t_0+ms_0)},\qquad
 \mathbb E\beta_f=2^{-t_0}.
\]
Average the affine expression
$X_f-(\epsilon/4)2^{-ms_0}\beta_f$ to choose $f$ such that, writing
$X=X_f$ and $\beta=\beta_f$,
\[
 X\ge(\epsilon/4)2^{-ms_0}\beta
          +(\epsilon/4)2^{-(t_0+ms_0)},\qquad
 \beta\ge X\ge(\epsilon/4)2^{-(t_0+ms_0)}
                \ge\tfrac14 2^{-2(m+1)h}.
\]
These are densities over all actual stars, not densities renormalized
by the generic tuples.

Suppose this $f$'s matching leaf set were $(r,e)$-pseudorandom.
To absorb the analytic error against half of the first selected
summand, it suffices to require
\[
 D_{\mathrm{inv}}2^{-(20/3)mh}
 \le (S^2/32)2^{-(t_0+2ms_0)}.
\]
Equivalently, the following fixed-parameter lower cutoff suffices:
\[
 \bigl((8/3)m-2+(3996m+2)\rho\bigr)h
       \ge\log_2(32D_{\mathrm{inv}}).
\]
Its coefficient is positive. This compares with the full selected
signal, including $\beta$, rather than with $S$ alone.
The selected lower bound and analytic upper bound would now imply
\[
 1\le8K_{\mathrm{inv}}2^{ms_0}\beta^{-1/T}
                  e^{m-2/T}/\epsilon
 \le8K_{\mathrm{inv}}2^{2/T}2^{-\lambda h},
\]
where
\[
 \lambda=2000m(\rho-\rho^2)-2m\rho-2(m+3)/T
 \ge m\rho\bigl(2000(1-\rho)-2.5\bigr)>0.
\]
Taking $h>(\log_2(8K_{\mathrm{inv}})+2/T)/\lambda$ is a contradiction.
By MZ Definition~2.1, failure of $(r,e)$-pseudorandomness provides
$\dim Q+\operatorname{codim}W=r$ and matching density greater than
$e$ on a nonempty zoom. The restriction $f|_W$ supplies the asserted
agreement. This uses the definition's actual dimensions and gives
agreement $>e$, not an unspecified constant times $e$.
All constants above are independent of $n$. Every ambient requirement
is an explicit lower bound, satisfied by $n=2J$ for the prescribed
$J$ and sufficiently large admissible $h$; there is no ambient upper
bound or required identity involving $\log\log n$.
\end{proof}

\begin{lemma}[Robust enlarged-ambient local application]\label{lem:robust-local}
Fix $m\ge2$, $0<\rho\le1/4000$ and $r=10m/\rho$, with integral test dimensions
$t=2(1-\rho)h$, $d=2h$. Put
\[
 S=2^{-2(1-1000\rho)hm},\qquad
 \epsilon'=2^{-2(1-1000\rho^2)h},\qquad C=\epsilon'/5.
\]
For sufficiently large admissible $h$ and $J=2^{2^{Ah^2}}$, a transverse
star test of density at least $8S$ in $U$, with $\dim U=3J$ and
$\dim H=J$, has fixed $a,c$ with $a+c\le r$ such that at least
$2^{-6h^2}$ of all uniform $a$-spaces $Q\subseteq U$ admit a
codimension-$c$ space $W\supseteq Q+H$ and a linear function respecting
$H$ with agreement at least $C$ on the transverse conditioned
Grassmann space. Here $A>0$ is fixed before $h$.
\end{lemma}
\begin{proof}
Apply Lemma~\ref{lem:inverse-explicit} at $n=2J$, retaining all its
fixed-parameter cutoffs on $h$ and explicit lower bounds on $n$.
It supplies agreement greater than $\epsilon'=e$ at input density
at least $S$. We now give the amplification and side-condition steps.

By Lemma~\ref{lem:complement}, the mean density over complements is
at least $8S$. Complements whose density $\epsilon_A$ is at least
$4S$ have mass at least $4S$, since the mean is at most $4S$ plus
that mass. Fix such a complement. Starting from its table, repeatedly
apply the inverse argument while the current density is at least
$\epsilon_A/2$. Add the resulting zoom to a union $X$ of leaf entries,
and independently replace every entry in $X$ by a uniform linear
function. The inverse threshold remains valid since
$\epsilon_A/2\ge2S$.

Here is the preservation event, including its ambient bound.
For each candidate $(Q,W',g)$ with dimensions bounded by $r$, either
$X$ has relative measure less than $2^{-2h}$ in the zoom, or the
fraction of the entries in $X$ agreeing with $g$ is at most
$2^{1-2h}$. Each refreshed entry agrees with a fixed $g$ with probability
$2^{-2h}$. The Chernoff bound and the lower bound
$|X\cap\operatorname{Zoom}[Q,W']|
 \ge2^{-2h}2^{(2h-r)(n-r-2h)}$
in the second case give a per-step failure probability at most
\[
 F_n=16(r+1)^2 2^{n(r+1)}
       \exp\!\left(-2^E/12\right),\qquad
 E=-4h+2+(2h-r)(n-r-2h).
\]
Indeed at most $16(r+1)^2 2^{n(r+1)}$ triples are needed: the Gaussian
counts for $Q,W'$ contribute at most $16\cdot2^{nr}$ and the number
of linear $g$ is at most $2^n$. The same bound holds conditionally on
any preceding history, since each refresh is independent.

Require $2^{1-2h}\le\epsilon'/2$. Before a new zoom is added, at most
this much of its agreement comes from previously refreshed entries;
this includes the alternative with relative measure below $2^{-2h}$.
Its unrefreshed fraction is therefore at least $\epsilon'/2$.
The zoom has ambient measure at least $2^{-rn}/4$ by the elementary
Gaussian bounds, so $X$ increases by at least
$\epsilon'2^{-rn}/8$. Thus no more than
$B_n=\lceil8\cdot2^{rn}/\epsilon'\rceil+1$ such steps are possible.
Choose the parameters so $B_nF_n<1/2$; a history with all preservation
events then exists. This requirement is satisfied for the prescribed
$J$: when $h\ge\max(r+4,16)$ and $n\ge8h+4r+16$, we have
$E\ge hn/2$, whereas $\log B_n+\log(16(r+1)^2 2^{n(r+1)})$
is $O_{m,\rho}(rn+h)$. Every selected function agrees with the original
table on at least $\epsilon'/2$ of its zoom.

At termination the acceptance has fallen by at least $\epsilon_A/2$.
It can change only if at least one of the $m$ leaf occurrences is in
$X$. Each leaf marginal is uniform, including when leaves repeat,
so $\mu(X)\ge\epsilon_A/(2m)$. For a fixed $a$-space $Q$, the
family of all $d$-spaces containing $Q$ has measure at most
$2^{4h^2-an}$. Count distinct $Q$ rather than algorithmic visits:
a repeated $Q$ with another zoom still covers only this family.
For each distinct useful $Q$, choose one witnessing $W'$ and assign
its codimension $c$. Let $N_{a,c}$ count the assigned pairs with
$\dim Q=a$, let $T_a$ be the number of all $a$-spaces in the complement,
and put $f_{a,c}=N_{a,c}/T_a$. Since $T_a\le4\cdot2^{an}$,
\[
 \frac{\epsilon_A}{2m}\le\mu(X)
 \le\sum_{a,c}N_{a,c}2^{4h^2-an}
 \le4\cdot2^{4h^2}\sum_{a,c}f_{a,c}.
\]
Thus $\sum_{a,c}f_{a,c}\ge\epsilon_A2^{-4h^2}/(8m)$.
Set these fractions to zero on bad complements and average over all
uniform complements. Good complements have mass at least $4S$ and
$\epsilon_A\ge4S$, so the sum of the averaged fractions is at least
$2S^2 2^{-4h^2}/m$. A single pigeonhole over at most $(r+1)^2$
dimension pairs gives one fixed $(a,c)$ whose success probability is
at least $2S^2 2^{-4h^2}/(m(r+1)^2)$, and hence at least the
conservative bound retained below:
\[
 \frac{2S^2}{m(r+1)^3}2^{-4h^2}.
\]
The pair is fixed after pigeonholing. We do not condition the marginal
law on a successful complement: successes form a subset of the full
uniform experiment. Its $Q$ marginal is uniform among $H$-disjoint
$a$-spaces. Extending to uniform $Q\subseteq U$ loses at most
$2^{a+1-2J}$. The sufficient bounds
\[
 h^2\ge4mh+\log_2(m(r+1)^3)+1,\qquad 2J\ge5h^2+r+2
\]
leave at least $2^{-5h^2-1}\ge2^{-6h^2}$ of all $Q$.
Finally set $W=W'\oplus H$ and extend $g$ by the prescribed side
conditions. For fixed $A,Q,W'$, projection to $W/H$ gives the same
uniform quotient law for the containing leaves in $W$ and $W'$;
the values on $H$ already agree. Hence their agreement events agree
and the retained $\epsilon'/2$ is stronger than $C=\epsilon'/5$.
This accounts for the uniform-$Q$ correction inside this lemma;
subsequent exclusions are applied to its already obtained lucky set.
\end{proof}
```

Write a for an advice dimension, 0<=a<=r, and c for a zoom-out
codimension, 0<=c<=r. Write d=2h. In the outer sampler each triple retains
all three coordinates with probability 1-beta, and otherwise retains a
uniformly chosen single coordinate. Thus the number of dropped blocks
D is Bin(J,beta), and dim(V)=3J-2D. Let P be the uniform distribution on
a-subspaces Q of U. Let P' be the marginal obtained by first sampling V,
then sampling a uniform a-subspace of V.

For J=2^(2^(A h^2)) and beta=A h^2/J, the advice statistical distance obeys

    SD(P,P') <= delta_adv := beta sqrt(J) 2^(a+4).

This is smaller than 2^(-100h^2) for sufficiently large h. Likewise the
KMS zoom-in exceptional fraction

    delta_zoom := sqrt(beta) J^(1/4)

and the conditional distance delta_zoom 2^(d+5) are smaller than
2^(-100h^2), after increasing the fixed lower bound on h. The condition
2^d beta<=1/8 is satisfied. Increasing A does not cause a circular choice:
A depends only on fixed decoding/outer constants, and h is chosen afterward.

Set T=h^4 and zeta=2^(-30h^2). The binomial tail has the explicit bound

    Pr[D>T] <= (e A h^2/T)^T <= 2^(-100h^2)

for sufficiently large h (round T to an integer if needed). Except on a
P'-mass at most 2^(-70h^2) of Q, Markov's inequality gives
Pr[D>T | Q]<=zeta. Passing from P' to P adds at most delta_adv to this
exceptional mass. Further, the set where P'(Q)<P(Q)/2 has P-mass at most
2 delta_adv, by the definition of statistical distance. Intersect these
good sets with the KMS good zoom-in set. The excluded P-mass is at most

    delta_zoom + 3 delta_adv + 2^(-70h^2) < 2^(-20h^2).

Fix a Q outside this exceptional set. For any V with D<=T, Bayes' rule
and the Gaussian binomial formula give

    Pr[V | Q]/Pr[V]
      = 1[Q subset V] / ( [dim(V) choose a]_2 P'(Q) )
      <= 2 [3J choose a]_2 / [3J-2D choose a]_2
      <= 8 * 2^(2aT).

The last inequality follows by factoring out 2^(2aD) in the product
formula; the remaining finite products are bounded by an absolute
constant because 3J-2D is much larger than a. This is a density bound
for the actual posterior, not an assumption that V remains unconditioned.

Now let W=W(Q) be any subspace containing Q, of codimension c<=r.
Once Q is fixed, W is fixed before V is sampled. Express W as the kernel
of a rank-c matrix. Failure of codim_V(W intersect V)=c means that some
nonzero linear combination of its rows has support entirely outside V.
For each of the at most 2^c-1 combinations, select one nonzero coordinate.
That coordinate is removed with probability at most beta. A union bound
therefore gives the unconditional estimate (2^c-1)beta, uniformly in W.
Applying the posterior density bound on D<=T, and then the tail bound,
gives, for this same Q,

    Pr[codim_V(W intersect V) != c | Q]
       <= 8 * 2^(2aT) (2^c-1) beta + zeta
       <= 2 zeta.

The last inequality holds for large h because J is double exponential in
h^2. The estimate is valid for every W(Q) of the permitted codimension;
there is no union over all W, no assumption that W is chosen independently
of Q, and no use of an unconditional rank estimate after conditioning.

The KMS distribution conditioned on Q is exactly the posterior needed
here. Indeed, the probability a uniform d-subspace L of V contains Q is

    1[Q subset V] [d choose a]_2 / [dim(V) choose a]_2.

The numerator is independent of V, so conditioning the joint (V,L)
sampler on Q subset L induces the same V posterior as sampling Q uniformly
inside V. This also explains why an unconditioned outer draw is invalid.

For the zoom-out, put b=d-a and p0=2^(-cb). On the rank-stable event,
the additional probability of L subset W, given V and Q, is

    p_V = [dim(V)-a-c choose b]_2 / [dim(V)-a choose b]_2
        = p0 (1 + O(2^(-J/2))).

This product estimate is uniform: dim(V)>=J always, while a,c,d are
O_{m,rho}(h). Under the uniform U sampler the corresponding probability
is at least p0/2 for large h. Conditioning two distributions at distance
Delta on an event of probability at least p0/2 changes their distance by
at most O(Delta/p0). Apply this with the KMS conditional distance
Delta=delta_zoom 2^(d+5).

Finally compare the posterior mixture with the mixture additionally
weighted by p_V. Rank-unstable V have posterior mass at most 2 zeta;
their contribution to the normalized weighted mixture is O(zeta/p0).
On the remaining V, p_V/p0 differs from one by O(2^(-J/2)). Hence for
any event concerning L, the difference between these two mixtures is

    O(2^(-J/2) + zeta/p0).

Both this expression and Delta/p0 are much smaller than 2^(-10h^2), since
p0>=2^(-2rh). Therefore agreement with a decoded function on a uniform
L satisfying Q subset L subset W transfers to the actual posterior
experiment with additive error below 2^(-10h^2). This supplies the
conditional-on-W step with the correct V distribution. It also supplies
the rank stability required when the two provers extend their functions.

### Decoder probability is measured in the same joint law

The outer advice consists of shared random vectors in V (MZ Section
3.2), and both provers take the span of the same first a vectors after
independently guessing a. Given linear independence, the span is uniform
among a-subspaces of V. The probability of dependence is at most
sum_{i=0}^{a-1} 2^(i-dim(V)) <= 2^(r-J). Thus the actual vector-advice law
and the ideal experiment V then uniform Q subset V differ in statistical
distance by at most 2^(r-J). This error is negligible compared with every
success term below; no alteration of the outer game is needed.

Fix the leaf-label assignment T1 after the imported clique-consistency
selection, with T2 the center-label assignment. A good first-prover question
U is one whose conditional inner-test density reaches the robust threshold
8S in the preceding lemma, where S=2^(-2(1-1000rho)hm). Write
Delta=2^(-2(1-xi)hm). After the already charged clique loss, the surviving
density is at least Delta/2. If Delta/4>=8S, the mass of good U is at
least Delta/4, since the mean is at most 8S plus that mass. The condition
Delta/S>=32 is exactly 2hm(xi-1000rho)>=5. It holds for sufficiently
large h with 1000rho<=xi/4. Thus the good-question mass remains
2^(-O_m(h)), with the amplification margin paid explicitly and no
additional complement-coupling error.

Fix a good first-prover question U. In the ideal joint experiment the
marginal law of Q is P', and the conditional law of V is exactly the
posterior analyzed above. The favorable advice set has P-mass at least
2^(-6h^2)-2^(-20h^2)-2^(r+1-2J). Passing to P' subtracts delta_adv,
so its P'-mass is at least 2^(-8h^2). For each such Q the expected
agreement under the actual posterior V is at least C-2^(-10h^2), hence
at least C/2. Since agreement is in [0,1], the posterior probability
that it is at least C/4 is at least C/4. Subtracting the rank-failure
probability 2 zeta leaves at least C/8 for large h.

These two probabilities multiply within the actual joint experiment:
P'(good Q) times Pr[good V | Q]. They are never converted to an
unconditional V success probability for a fixed Q. In particular, the
factor 8*2^(2a h^4) was used solely to upper-bound a rank-failure event;
its reciprocal is not a loss in the decoded success bound. The
independent-vector correction subtracts at most 2^(r-J) from the final
joint success, again negligible. The threshold-ladder strategy below supplies the maximal-extension step.
### Total tables and transverse subspaces

The source vertices L plus H_U require L intersect H_U={0}. For each
U, extend the induced table to all d-subspaces by assigning the zero
linear function on otherwise undefined entries. The robust enlarged-ambient local lemma above is applied with its
proved side-condition/transversality
hypothesis. Its resulting agreement on the full conditioned Grassmann
space, or equivalently the agreement after charging the exceptional
entries, loses a negligible amount quantified here.

If Q intersect H_U={0} and W contains Q+H_U with codimension at most r,
a uniform d-subspace L between Q and W fails transversality only if
L/Q meets (H_U+Q)/Q nontrivially. A union bound over nonzero vectors
of this J-dimensional image bounds this probability by

    2^(J+d-dim(W)+1) <= 2^(-2J+d+r+1).

This follows from Pr[z in a uniform b-subspace of an n-space]
=(2^b-1)/(2^n-1), and applies with an extra factor at most two if a
preceding distribution was already conditioned on transversality.
It is negligible compared with C.

For each second-prover question V fix an arbitrary legitimate completion
U_0(V) containing V. Define its total table on every d-subspace L of V
by T1[L+H_{U_0}]|L when transverse, and by zero otherwise. This definition
depends only on V and the fixed global assignment table. Whenever L is
transverse to both H_U and H_{U_0}, the source clique-consistency relation
identifies the two values. No equality is asserted on other entries.

Here are explicit charges for those other entries in the actual joint
law for a fixed original U. On D<=T, dim(V)>=3J-2T. For uniform Q subset
V, the probability Q meets H_{U_0(V)} nontrivially is at most
2^(a+J-dim(V)+1) <= 2^(-2J+2T+r+1). This bound is valid although U_0
is selected after V. Including the tail gives joint probability at most
2^(-100h^2)+2^(-2J+2T+r+1). By Markov, except on P'-mass at most
2^(-69h^2), its posterior probability for fixed Q is at most zeta.
Passing to P adds delta_adv. Remove these Q from the good advice set;
the total removed advice mass still fits the bound 2^(-20h^2).

For remaining Q,V with D<=T, rank stability, and Q disjoint from both
side-condition spaces, take L uniform between Q and W intersect V.
For either side-condition space the same quotient union bound gives
nontransversality probability at most

    2^(J+d-(dim(V)-r)+1) <= 2^(-2J+2T+d+r+1).

For H_{U_0} not contained in W intersect V use its intersection with
that space; its dimension is at most J, which only improves this bound.
Thus replacing either total table by the actually defined transverse
values costs at most twice this bound on good V, plus the posterior
tail and exceptional probabilities O(zeta). These are below
2^(-10h^2). Enlarge the finite lower bound on h to absorb all such
additive errors simultaneously. In the subsequent agreement ledger
one may use expected agreement C/2, good-V agreement C/4, and good-V
probability C/8 as already budgeted. No undefined table entry or
unproved identity on nontransverse L is used.
### Explicit threshold ladder for maximal extensions

A single arbitrarily lowered threshold does not guarantee maximality.
Instead the second prover guesses j uniformly from {0,...,r} and uses
B_j=C/(4*5^j). For a favorable V, begin with (W(Q) intersect V,g restricted to W(Q) intersect V),
which has codimension at most r and agreement at least B_0=C/4. At
stage j, if the pair is (B_j,1/5)-maximal, stop. Otherwise Definition
5.4 supplies a proper extension of the pair with agreement at least
B_j/5=B_{j+1}. Replace the pair by that extension. Each replacement
strictly decreases codimension, so this process stops by stage r,
at latest at the whole space, where no proper extension exists.

Thus at one of these r+1 thresholds a maximal pair exists whose function
extends the first prover's restriction. The second prover enumerates all
maximal pairs of codimension at most r at the guessed threshold and
chooses uniformly; this is a strategy for a value bound, not a polynomial
algorithm used by the reduction. The maximal-pair counting contract bounds each such list by
B_j^(-2)*2^(O_{m,rho}(h))=2^(O_{m,rho}(h)). Its threshold hypothesis holds:
the local agreement is C=2^(-2(1-1000rho^2)h)/5, so

    B_r / 2^(-2(1-rho^3)h)
       = 2^(2(1000rho^2-rho^3)h)/(20*5^r) >= 1

for sufficiently large h (take rho<1). Codimension is at most the
source local bound r<=10m/rho; the advice dimension is also within
the narrower MZ24 counting contract. This costs the additional constant factor 1/(r+1), with
no single-threshold existence assumption. The first prover takes its decoded linear function g on W(Q), which
respects the equation side conditions, and extends it uniformly to U.
The second prover extends its selected maximal-pair function uniformly to
V. For the successful choice, that function extends g restricted to
W(Q) intersect V. Rank stability gives codim_V(W(Q) intersect V)=c,
where c=codim_U W(Q)<=r. The restriction to V of a uniform extension of
g to U is uniform among the 2^c extensions of this common restriction:
the quotient map V/(W(Q) intersect V) -> U/W(Q) is an isomorphism.
Thus it agrees with the second prover's chosen extension on V with
probability 2^(-c)>=2^(-r). The first prover's assignment satisfies all
outer equations because its extension preserves g on H_U. This proves
the claimed random-extension success cost.
## Completing the modified PCP parameter order

Fix m>=2 and a desired exponent slack xi>0; set rho<=min(xi/4000,1/4000), choosing it positive and rational and
shrinking it further if necessary to meet the imported local theorems. Use the same
star-query construction as MZ, with the new J,beta above. The following
table checks every ambient/repetition-dependent loss used in its decoding
argument. Local Grassmann decoding and the maximal-zoom-out counting
theorem are imported; the numerical parameter extension is argued here.

| Use | Control under the replacement |
|---|---|
| Ambient dimensions in local decoding | Counting uses dim(V)>=J>=2^h. Complement decoding has ambient n=2J and its query law is exact. The robust local lemma retains the matrix-rank, spectral, randomization-history and uniform-Q bounds; each ambient error improves with J. |
| Duplicate clique choices | The source Gaussian-binomial comparison decreases exponentially in J; for large h the union over m^2 pairs is at most 2^(-J). |
| Lucky advice meeting H_U | Its uniform probability is at most 2^(r+1-2J). |
| Advice/zoom-in covering | The bounds above and their exceptional Q sets are less than 2^(-20h^2), below the local decoding lucky mass 2^(-6h^2). |
| Zoom-out and rank steps | The posterior calculation above gives error below 2^(-10h^2), below the decoded agreement C>=2^(-O_{m,rho}(h)). |
| Number of maximal zoom-outs | The imported bound is 2^(O_{m,rho}(h)) for the relevant agreement and codimension; its constants do not depend on J. |
| Random extensions | Their agreement cost is at most a factor 2^r, since codimensions are bounded by r. |

```latex
Write the good-question mass as at least $K_U^{-1}2^{-B_Uh}$ and the
maximal-list bound as at most $K_M2^{B_Mh}$, with $K_U,K_M\ge1$ and
$B_U,B_M\ge0$. These name the bounds just established and imported;
their constants depend on $m,\rho$, not $A,J$ or the later YES error.
The displayed decoding strategy, with its previous losses already
charged, succeeds before the vector-law correction with probability
at least $K^{-1}2^{-8h^2-Bh}$, where
\[
 K=40K_UK_M(r+1)^3 2^r,\qquad B=B_U+B_M+2.
\]
Here $C/8\ge2^{-2h}/40$, the three dimension/threshold guesses cost
at most $(r+1)^3$, and the extension cost is at most $2^r$.
For $h\ge\max(1,B+\log_2K)$ this is at least $2^{-9h^2}$.
Taking $J\ge9h^2+r+1$, the vector-law error $2^{r-J}$ leaves at
least $2^{-9h^2-1}\ge2^{-10h^2}$. No exponential-in-$J$ success
factor is paid.
```

The fixed outer NO gap gives success at most 2^(-kappa beta J), with
kappa>0 depending on the fixed advice size and outer NO gap, not on the
later outer YES error. Choose an integer A before h:

    A > 20/kappa.

```latex
Then the outer upper bound, even including the factor two for legitimate
conditioning ensured by the padding below, is at most
$2\cdot2^{-\kappa Ah^2}<2^{-10h^2}$, contradicting decoded success.
All lower bounds on $h$ may depend on this fixed $A$. Thus the modified
PCP has soundness at most $R^{-(1-\xi)m}$, where $R=2^{2h}$.
```

Only after fixing m,xi,h,J,beta do we fix any desired positive constant
PCP completeness error tau. Select the outer 3-Lin YES error

    epsilon_1 <= tau / (100(m+1)J).

The starting hardness theorem allows every fixed positive epsilon_1 with
an absolute NO gap. In particular, this does not require exactly
satisfiable linear equations to be NP-hard. Its reduction exponent may
depend on epsilon_1, which is allowed because every parameter here is a
constant independent of the input length.

To account for discarded illegitimate tuples, take sufficiently many
disjoint copies of the outer instance so their probability a is at most
min(tau/100,1/4). The bound is O(J^2/N_outer) with a constant from the
bounded occurrence condition. Copies preserve the value and degree bound.
The number required depends only on the already fixed parameters; for
an input of length n the padded size is O(n+N_min), still polynomial.
Conditioning on legitimate U multiplies a failure probability by at most
1/(1-a). The sampler's marginal for each clique-resampled U'_i is uniform
over legitimate U: the initial vertex is uniform, and uniform resampling
within its equivalence class preserves that measure. All relevant spaces
have the same dimensions and number of transverse extensions.

An honest global labeling satisfies the composed constraint whenever the
equations in the original U and all m resampled U'_i are satisfied.
Union bounding gives failure at most

    (m+1)J epsilon_1/(1-a) <= tau/75 < tau.

Using all m+1 blocks is deliberately conservative; no equality between a
single-block bound and the multi-query acceptance event is needed. This
establishes the required parameter order: for each fixed m,xi and each
sufficiently large h, every fixed positive tau is available without
increasing R. J and the source input-size threshold can be very large,
and all are charged as fixed constants.

The construction and enumeration cost is N_outer^(O_{m}(J)) with constants
depending on these choices, plus the starting outer reduction. It is not
a polynomial with a uniform exponent when L, h or tau vary with input
length. No superconstant-parameter hardness claim is made.

## From the modified PCP to an explicit realizable list

Use HN's star-projection compilation and its occurrence weights, retaining
repeated leaf-variable consistency as in its Lemma 4.6. It gives formulas
with at most (m+1)R leaves, a normalized honest budget s, and a constant
NO satisfaction bound 3/4 up to weight sigma s, where we may safely take
the explicit integer

    sigma = floor(R^(1-1/m)/16), xi=1/m^2.

For implementation this floor is computed by integer root comparison;
no irrational number is an encoded weight. The constant 1/16 is smaller
than the coefficient in the source's list-decoding bound. For sufficiently
large R, sigma>=8. Set q=floor(sqrt(m)) and take an AND of q independently
sampled base formulas. Put

    Gamma = 2(3/4)^q, epsilon = Gamma/(16 sigma),
    tau = epsilon/(4q).

The modified PCP above permits this tau after R has been fixed. The
AND-product YES failure is at most q tau=epsilon/4; the NO satisfaction
fraction is at most (3/4)^q=Gamma/2. The local leaf bound is q(m+1)R.

Let N_0 be the number of monotone variables. Materialize the finite
sampling support if necessary; for fixed parameters it has polynomial
size in the outer input. Its rational probabilities and occurrence
weights have polynomial bit descriptions. A positive atom is a product
of a fixed number of inverse-polynomial choices, so positive variable
weights and s are inverse-polynomially bounded. Adding rational numbers
may enlarge a common denominator, which is handled separately below.

Construct a bounded-random-bit sampler whose distribution has statistical
distance at most epsilon/8 from the exact product distribution. One
implementation enumerates its S atoms and rounds cumulative rational
probabilities to a dyadic grid with at least log2(8S/epsilon) bits. Charge
the support enumeration and rational arithmetic. This is polynomial for
fixed L; it is not an oracle for an exponentially large support.

Choose a natural P with 1/epsilon<=P; epsilon is positive. Since epsilon
is rational, P=ceil(1/epsilon) can be computed by integer division and
remainder on its numerator and denominator. Use the conservative count

    T=32(N_0+11)P^2,    M=2^(clog_2 T),
    (N_0 ln 2+ln 12)/(2(epsilon/8)^2) <= T <= M < 2T.

Here clog_2 T is the least natural exponent whose power of two is at
least T. The constructor uses only natural arithmetic. The displayed
analytic bound follows from ln 2<=1, ln 12<=11 and 1/epsilon<=P; it is
a proved comparison, not a real-number computation required by the
sampler. This one count already gives sampling success at least 5/6,
and therefore also the required 2/3. It is the least qualifying power
of two for T, not necessarily for the exact logarithmic threshold.
For fixed L the previously chosen positive rational epsilon is fixed,
so this choice of P is constant with respect to the outer input, and
M<64(N_0+11)P^2 bounds the list length. Support enumeration and rational
arithmetic costs still have to be charged as above. The formal count
and probability bounds do not certify an encoded machine runtime.

Draw M independent formulas from this sampler. Hoeffding's inequality and
a union bound over 2^N_0 assignments imply, with probability at least 2/3,
that all empirical satisfaction fractions differ from their exact product
probabilities by at most epsilon/4, including the sampling-distribution
error. Hence the list's YES failure is at most epsilon/2, and its NO
acceptance is at most Gamma/2+epsilon/4 < Gamma. The exception lemma may
therefore use the conservative error budget epsilon. Its condition
epsilon sigma<=Gamma/2 holds with a factor-eight margin.

Apply that lemma to this actual list. The output satisfies all constraints
in its YES case, with ratio floor(sigma/4), threshold 2 Gamma, and at most
q(m+1)R+1 leaves per formula. Failure of the randomized reduction occurs
only in the sampling event already bounded by 1/3. The completed list
has an exact uniform sampler using log2(M) random bits. In particular,
the later learning reduction sees epsilon=0 exactly; it does not inherit
the approximate sampler used to construct the list.

## Rational-weight control and learning transfer

Polynomial bit lengths alone do not make all weights integral multiples
of 1/poly(n). We supply a rounding step before any use of fixed-length
strings w_i lambda in the learning reduction. Let v_i be the final
normalized weights on N' variables and t its YES budget. Choose the least power
of two D>=8(N'+1)/t, set a_i=ceil(D v_i), A_0=sum_i a_i, and

    B_0=min(A_0, ceil(D t)+N'), v'_i=a_i/A_0, t'=B_0/A_0.

A YES assignment remains feasible, since its integer weight is at most
D t+N'. Conversely, any assignment with v'-weight at most
(sigma_new/2)t' has original v-weight at most

    (sigma_new/2) B_0/D
      <= (sigma_new/2)(t+(N'+1)/D)
      <= (9/16) sigma_new t < sigma_new t.

Thus the NO acceptance threshold is unchanged if the gap factor is
rounded down to floor(sigma_new/2). Formula leaves and satisfaction are
unchanged. D and A_0 are polynomial numeric quantities because t has an
inverse-polynomial lower bound; all new weights and the budget share the
polynomial common denominator A_0. The clipping in B_0 guarantees t'<=1
and does not weaken either displayed inequality.

Represent the power-of-two list by its exact sampler. Every monotone
formula with L leaves admits the source's L-bit-total secret-sharing
construction. HN Lemma 5.1 explicitly allows epsilon=0: it keeps that
completeness error, multiplies the NO threshold by five, loses a factor
0.49 in the size gap, and uses advice bound

    L + 2 ceil(log2(L+1)) + c_U.

Its length parameter can be chosen as a polynomial multiple of A_0, so
all strings of length v'_i times that parameter have integral lengths.
The parameter is also increased by a polynomial factor to meet its stated
description and soundness bounds. These adjustments are polynomial in
the actual instance size. Perfect completeness holds for every randomness
string of this transfer; its additional randomized failure probability is
on the NO side. The conservative list count above already gives success
at least 5/6; combine this with the transfer's sufficiently small
failure probability to obtain a randomized many-one reduction with
success at least 2/3. Finitely many small inputs can be handled by a fixed
truth table, a constant cost depending on the fixed parameters.

## Final asymptotic parameter choice

For each fixed sufficiently large target leaf bound L, consider integers
m>=256 with m<=sqrt(log2 L). Let q=floor(sqrt(m)) and

    h(L,m)=b_m floor( log2((L-1)/(q(m+1)))/(2b_m) ), R=2^(2h).

Additionally require b_m<=sqrt(log2 L). Require h(L,m) to exceed every
fixed lower bound used above for that m
and xi=1/m^2, including sigma>=8 and all numerical error inequalities.
Choose the largest admissible m. Every fixed m is admissible for all
sufficiently large L, so m(L) tends to infinity. The finite selection
does not assert a polynomial-time algorithm uniform in L; for each fixed
L it fixes the constants of a uniform polynomial-time reduction on inputs.
The same fixed-parameter convention is used in the revised source.

The final leaf bound is at most L by construction. Moreover,

    log R = log L - O(log(m+1)+b_m) = log L - o(log L),
    log sigma / log L -> 1,
    Gamma=2(3/4)^floor(sqrt(m)) -> 0.

All floor operations, the exception lemma, weight rounding and learning
transfer lose only constant factors in sigma. They therefore preserve
sigma=L^(1-o(1)). For the learning target with advice cap a, choose
L=a-2 ceil(log2(a+1))-c_U; for large a this is positive and the advice
overhead fits within a. Also L/a tends to one, preserving the exponent.

Theorem 1 follows with the explicit parameters

    sigma_L=floor(floor(sigma/4)/2),    gamma_L=2 Gamma,

where sigma, Gamma, m, h and R are selected above. For sufficiently large
L these are in the promised ranges. The conservative natural list count
above gives sampling success at least 5/6. Corollary 2 follows
from the stated HN transfer with its residual error made at most 1/6; the
combined success is at least 2/3. The exact sampler and complete repaired
YES witness ensure that the learning error parameter is exactly zero.
This completes both proofs.

## Research and review disclosure

This manuscript was developed through AI-assisted mathematical derivation,
source challenge, independent agent mathematical review, dependency audit,
and source/significance assessment under Quantyra Research. These are
informal AI reviews, not independent human peer review or Lean verification.
The source challenger contributed to the argument and is not counted as
an independent mathematical verifier. Review roles, findings, and limits
are disclosed in [REVIEW.md](REVIEW.md). Bibliographic versions and imported
inputs are recorded in [SOURCES.md](SOURCES.md).

```latex
\appendix
\section{Finite binary matrix hypercontractivity}\label{app:binary-hc}
This appendix supplies the analytic inequality used in
Lemma~\ref{lem:inverse-explicit}. We reconstruct the binary finite-matrix
argument, including its auxiliary estimates, rather than import a
hypercontractive theorem. The underlying method is due to Ellis, Kindler
and Lifshitz, and its globalness and dyadic applications to Evra, Kindler
and Lifshitz.\footnote{The versions used for comparison are
Ellis--Kindler--Lifshitz, \emph{An analogue of Bonami's lemma for functions
on spaces of linear maps, and 2-to-2 games}, arXiv:2209.04243v1,
\url{https://arxiv.org/abs/2209.04243v1}; and
Evra--Kindler--Lifshitz, \emph{Polynomial Bogolyubov for special linear
groups via tensor rank}, arXiv:2404.00641v2,
\url{https://arxiv.org/abs/2404.00641v2}. The first authors are different.
The proof below uses the sufficient constants $6,196$ and an auxiliary
weight $6d$, and retains the final constants $100,103,200,500$. It does not
assert the stronger intermediate displays in those versions.}
This is an ordinary mathematical proof, not a claim of Lean verification
or novelty. Other upstream PCP, compilation and learning inputs of the
manuscript remain as stated.

\begin{theorem}[Binary Boolean matrix inequality]\label{thm:binary-hc}
Let $F:\operatorname{Mat}_{n,D}(\mathbb F_2)\to\{0,1\}$ and
$0\le\delta\le1$. Suppose every consistent restriction
$MU=V_0$, $XM=Y_0$ of nominal budget $r$ has uniform conditional density
at most $\delta$. The nominal budget counts the columns of $U$ plus the
rows of $X$; dependent and zero equations are allowed. For $0\le i\le r$
and every dyadic integer $p\ge4$, the rank-$i$ Fourier projection satisfies
\[
 \|F^{=i}\|_p\le 2^{500i^2p}\delta^{1-2/p}.
\]
All measures are normalized probabilities. There is no basis-invariance,
full-rank-conditioning or aspect-ratio hypothesis.
\end{theorem}
We prove the theorem after developing its finite ingredients. Dimensions
in this appendix may be zero, and all functions other than the final
indicator may be complex valued.

\subsection{Characters, restrictions and actual derivatives}
Put $\mathcal H(V,W)=\operatorname{Hom}(V,W)$ for binary vector spaces.
Its dual characters are indexed by $Y:W\to V$:
$\chi_Y(M)=(-1)^{\operatorname{Tr}(YM)}$. The matrix trace is in
$\mathbb F_2$. Its pairing is nondegenerate (test a nonzero matrix entry
against the transposed elementary matrix), so character orthogonality
gives Fourier inversion and Parseval with
$\widehat f(Y)=\mathbb E_M f(M)\chi_Y(M)$.
Degree means maximum rank of a nonzero Fourier frequency. For subspaces
$A\le V$, $B\le W$, write $q_A:V\to V/A$ and $j_B:B\to W$ for the
canonical maps, and set
\[
 R_{A,B,T}f(N)=f(T+j_BNq_A),\qquad
 |(A,B)|=\dim A+\operatorname{codim}_W B.
\]
Every average on the restriction is uniform on $\mathcal H(V/A,B)$.
The ordinary filter $P_{A,B}$ keeps frequencies with
$A\le\operatorname{im}Y$ and $\ker Y\le B$. The hybrid filter
$L_{A,B}$ instead keeps
\[
 A\le\operatorname{im}Y,\qquad Y^{-1}(A)\le B.
\]
Define $D_{A,B,T}=R_{A,B,T}L_{A,B}$ and the influence
$I_{A,B,T}(f)=\|D_{A,B,T}f\|_2^2$.

Cyclic trace gives
$R_{A,B,T}\chi_Y=\chi_Y(T)\chi_{q_AY|B}$.
For a selected hybrid frequency,
$\ker(q_AY|B)=Y^{-1}(A)$ has dimension $\dim\ker Y+\dim A$.
Consequently its rank is $\operatorname{rank}Y-|(A,B)|$.
Thus an order-$s$ derivative annihilates levels below $s$, and for
$j\ge s$,
\[
 D_{A,B,T}(f^{=j})=(D_{A,B,T}f)^{=j-s}.
\]
The below-order assertion is a separate zero case, not truncated
natural subtraction. Raw restrictions only decrease rank. Products have
additive degree bounds, since $\chi_Y\chi_Z=\chi_{Y+Z}$ and
$\operatorname{rank}(Y+Z)\le\operatorname{rank}Y+\operatorname{rank}Z$.

If $A_2\le A_1$ and $B_1\le B_2$, a frequency passes the selector for
$(A_1,B_1)$ precisely when it passes that for $(A_2,B_2)$ and the induced
frequency passes that for $(A_1/A_2,B_1)$. For the forward implication,
preimages of $A_1$ lie in $B_1$ and supply representatives for every
vector of $A_1/A_2$. Conversely, quotient representatives and
$A_2\le\operatorname{im}Y$ give $A_1\le\operatorname{im}Y$; if
$Yw\in A_1$, choose $z\in B_2$ with $Yz=Yw$ modulo $A_2$.
Then $w-z\in Y^{-1}(A_2)\le B_2$, and the second selector puts $w\in B_1$.
Character phases therefore prove the exact composition
\[
 D_{A_1/A_2,B_1,S}D_{A_2,B_2,T}
   =D_{A_1,B_1,T+j_{B_2}Sq_{A_2}}.                 \tag{A1}
\]
All quotient identifications here and below are canonical. In particular
$D_{0,W,T}$ is translation, not identity unless $T=0$.
Translation and finite Fubini also prove
\[
 \mathbb E_T\|D_{A,B,T}f\|_2^2
   =\|L_{A,B}f\|_2^2
   =\sum_{Y\text{ selected}}|\widehat f(Y)|^2.       \tag{A2}
\]
At fixed $T$, frequencies may coalesce, so the last equality is not
asserted without the average.

We also need a different derivative. Write $X\preceq Y$ when
$\operatorname{rank}Y=\operatorname{rank}X+\operatorname{rank}(Y-X)$.
Equivalently, $\operatorname{im}X\le\operatorname{im}Y$ and $X$ agrees
with $Y$ on $Y^{-1}(\operatorname{im}X)$. Indeed rank additivity gives
complementary images; conversely the agreement condition forces
$\operatorname{im}(Y-X)\le\operatorname{im}Y$ disjoint from
$\operatorname{im}X$, and their sum contains $\operatorname{im}Y$.
Let $L_X$ keep $Y\succeq X$ and
$D_{X,T}=R_{\operatorname{im}X,\ker X,T}L_X$, with $D_X=D_{X,0}$.
For rank-$k$ $X$, choose splittings making $X=\left[\begin{smallmatrix}I&0\\0&0\end{smallmatrix}\right]$.
For a fixed induced frequency $Z:\ker X\to V/\operatorname{im}X$ of
rank $l$, the selected original frequencies are exactly
\[
 Y=\begin{pmatrix}I+uC&uZ\\ C&Z\end{pmatrix},
 \quad u:\operatorname{im}Z\to\operatorname{im}X,
 \quad C:\operatorname{im}X\to\operatorname{im}Z.     \tag{A3}
\]
Their number is $2^{2kl}$. To check this, the off-diagonal blocks of
$Y-X$ must factor through $Z$ and land in its image; rank additivity
forces the remaining block $uC$. Conversely choose a lift $v$ with
$Zv=C$; then $Y-X=[u;I]Z[v,I]$ has rank $l$, whereas elimination gives
$\operatorname{rank}Y=k+l$. The formula is independent of the lift.
Equivalently, the complementary images and kernels from rank additivity
force these same blocks. Thus $D_X$ lowers degree by $k$, with zero for
levels below $k$.

\subsection{A weighted fourth-power estimate without contraction}
For degree-at-most-$d$ $f$, put $E=\|f\|_2^2$,
$a_X=\sum_{Y\succeq X}|\widehat f(Y)|^2$, and $e_X=\|D_Xf\|_2^2$.
Cauchy--Schwarz on the fibers (A3) gives
$e_X\le2^{2k(d-k)}a_X$ for $k=\operatorname{rank}X\le d$; for $k>d$
both are zero. Since $a_X\le E$,
$e_X^2\le2^{4k(d-k)}Ea_X$.
For a fixed rank-$j$ $Y$, its rank-$k$ predecessors correspond to rank-$k$
projections on $\operatorname{im}Y$, by $X=QY$. Choosing the image of
$Q$ and a complementary kernel counts exactly
${j\brack k}_2\,2^{k(j-k)}$. The Gaussian product formula gives
${j\brack k}_2\le4\,2^{k(j-k)}$: its denominator product exceeds
$1/4$, since its first three factors give $21/64$ and the remaining
product is at least $1-\sum_{a\ge4}2^{-a}=7/8$.
The $k=0$ count is exactly one. Interchanging finite sums now yields
\[
 \begin{split}
 \sum_X2^{-6d\operatorname{rank}X}\|D_Xf\|_2^4
 &\le E^2\left(1+4\sum_{k\ge1}2^{-6k^2}\right)\\
 &\le\frac{67}{63}E^2\le2E^2.                       \end{split}\tag{W6}
\]
Indeed the coefficient at a rank-$j\le d$ frequency has exponent
$-6dk+4k(d-k)+2k(j-k)\le-6k^2$.
At $d=0$ the sum is exactly $E^2$.

This argument is necessary: $D_X$ is not a contraction. In fact the
weight-$4d$ fourth-power claim in the pinned Ellis--Kindler--Lifshitz
version fails for the stated operators. For $V=W=\mathbb F_2^d$ and
$f=\sum_{Y\in\mathrm{GL}_d}\chi_Y$, write $G_d=|\mathrm{GL}_d|$.
Then $E=G_d$, and every rank-one $X$ has
$e_X=2^{4(d-1)}G_{d-1}$ by (A3). There are $(2^d-1)^2$ such $X$, and
$G_d=(2^d-1)2^{d-1}G_{d-1}$. Their contribution to the weight-$4d$
sum divided by $E^2$ is $2^{2d-6}$, already $4$ at $d=4$.
We use (W6); the later induction has enough slack for it.

\subsection{Degree reduction from two convolution classes}
We prove the sufficient ordinary-filter inequality
\[
 \frac{\|f\|_4^4}{162}\le2^{6d^2}\|f\|_2^4+
 \sum_{(A,B)\ne(0,W)}2^{7d(\dim A+\operatorname{codim}B)}
                       \|P_{A,B}f\|_4^4.             \tag{DR6}
\]
Write $a_Y=\widehat f(Y)$, $b_Y=|a_Y|$ and
$\|f\|_4^4=\sum_X|\sum_{Y+Z=X}a_Ya_Z|^2$.
All contributing $Y,Z$ have rank at most $d$, and $X$ has rank at most
$2d$. Say $M=A\oplus C$ if $M=A+C$ with additive ranks.
Let $\mathcal F_1(X)$ consist of pairs admitting
$Y=A\oplus C$, $Z=B\oplus C$, $X=A\oplus B$.
Let $\mathcal F_2(X)$ consist of pairs for which
\[
 \operatorname{im}X\cap\operatorname{im}Y\cap\operatorname{im}Z\ne0
 \quad\text{or}\quad
 \ker X+\ker Y+\ker Z\ne W.
\]
These classes cover all pairs. To prove the assertion outside the second
class, put $K_M=\ker M$. One has
$(K_Z+K_X)\cap K_Y=K_Z\cap K_Y$: if $w=u+v\in K_Y$ with
$u\in K_X$, $v\in K_Z$, then $Zu=Yu=Yv=Xw$ lies in the zero triple
image intersection. Define $B$ to equal $Z$ on $K_Y$ and zero on
$K_Z+K_X$, and symmetrically $A$ to equal $Y$ on $K_Z$ and zero on
$K_Y+K_X$. These are well defined on $W$, and checking on the three
kernels gives $X=A+B$ and $C=Y+A=Z+B$. Their images lie respectively in
the pairwise image intersections, so are pairwise disjoint. On $K_Z$,
$K_Y$, $K_X$ the triples $(A,B,C)$ are $(Y,0,0)$, $(0,Z,0)$,
$(0,0,Y)$; since these kernels span $W$, the required image sums are
onto, proving the direct decompositions.

Put $H_X=\sum_{\mathcal F_1(X)}b_Yb_Z$ and
$O_X=\sum_{\mathcal F_2(X)}a_Ya_Z$. The classes can overlap; partition
instead into $\mathcal F_2$ and its complement. The convolution is then
bounded in absolute value by $H_X+|O_X|$. Consequently its squared sum
is at most $2\sum H_X^2+2\sum|O_X|^2$.

For the first class use independent uniform signs $x_A,y_C$, indexed by
two disjoint copies of all maps of rank at most $d$, including zero.
The real Boolean polynomial
\[
 \Phi(x,y)=\sum_{A\oplus C} b_{A+C}x_Ay_C
\]
has degree two. A rank-$r$ map has at most $2^{r^2}$ direct
decompositions: the first summand factors through its kernel quotient
and takes values in its image. Thus
$\|\Phi\|_2^2\le2^{d^2}\|f\|_2^2$.
The elementary Boolean estimate $\|\Phi\|_4^4\le81\|\Phi\|_2^4$
needs no imported hypercontractivity: for real $G=g+xh$, expansion and
Cauchy--Schwarz give
$\|G\|_4^4\le\alpha^4+6\alpha^2\beta^2+\beta^4
\le(\alpha^2+3\beta^2)^2$, where
$\alpha=\|g\|_4$, $\beta=\|h\|_4$.
Induction on the sign variables yields
$\|G\|_4^2\le\sum_S3^{|S|}\widehat G(S)^2$, proving the estimate.

Let $h(A,B)=\sum_C b_{A+C}b_{B+C}$ with both sums direct.
Then $H_X\le\sum_{A\oplus B=X}h(A,B)$. There are at most
$2^{4d^2}$ decompositions of $X$, so
$\sum_XH_X^2\le2^{4d^2}\sum_{A\oplus B}h(A,B)^2$.
For $A\ne B$, the coefficient of $x_Ax_B$ in $\Phi^2$ is
$2h(A,B)$; it dominates the two ordered-pair squares. For a direct pair
with $A=B$ one has $A=B=0$, and $h(0,0)$ is at most the constant
coefficient of $\Phi^2$. All these coefficients are nonnegative.
Parseval therefore gives
\[
 \sum_XH_X^2\le2^{4d^2}\|\Phi\|_4^4
                    \le81\,2^{6d^2}\|f\|_2^4.       \tag{A4}
\]

For the second class preserve complex coefficients and their
cancellations. Set $\alpha_k=(-1)^{k+1}2^{k(k-1)/2}$ for $k\ge1$.
For a $t$-space,
$\mathbf1_{t>0}=\sum_{k=1}^t{t\brack k}_2\alpha_k$.
This follows by putting $z=-1$ in
$\prod_{l=0}^{t-1}(1+2^lz)
=\sum_k{t\brack k}_2\,2^{k(k-1)/2}z^k$.
The product identity follows inductively from
${t\brack k}_2={t-1\brack k}_2+2^{t-k}{t-1\brack k-1}_2$,
obtained by intersecting subspaces with a fixed hyperplane.
Apply the indicator identity to the triple image intersection and to
the quotient by the sum of kernels, and use inclusion--exclusion.
With $\alpha_{i,0}=\alpha_i$, $\alpha_{0,j}=\alpha_j$,
$\alpha_{i,j}=-\alpha_i\alpha_j$ for $i,j>0$, this gives exactly
\[
 O_X=\sum_{\substack{(i,j)\ne(0,0)\\
 A\le\operatorname{im}X,\ \dim A=i\\
 B\ge\ker X,\ \operatorname{codim}B=j}}
       \alpha_{i,j}\widehat{(P_{A,B}f)^2}(X).         \tag{A5}
\]
Terms with $i>d$ or $j>d$ vanish. For the others, the number of pairs
$A,B$ is at most $2^{2d(i+j)}$, because $\operatorname{rank}X\le2d$;
moreover $|\alpha_{i,j}|^2\le2^{d(i+j)}$.
Weighted Cauchy--Schwarz with weight $2^{7d(i+j)}$ has remaining factor
at most
$\sum_{i,j\ge0,(i,j)\ne(0,0)}2^{-4d(i+j)}<1$ for $d\ge1$
(at $d=1$ it is $31/225$).
Summing (A5) over $X$ and using Parseval bounds
$\sum_X|O_X|^2$ by the weighted sum in (DR6).
Together with (A4), division by $162$ proves (DR6).
For $d=0$ it is the constant-function identity with a weakened
coefficient. No rank-$d$ bound on the convolution frequency $X$ was used.

\subsection{Exact transfers and the fourth-moment induction}
Fix $A\le V$, $B\le W$. For a frequency $Y$ selected by $P_{A,B}$,
put
\[
 C=Y(B)\cap A,\qquad H=B+Y^{-1}(A),\qquad R=q_CY|H.
\]
Define $X(b+z)=Yz+C$ for $b\in B$, $z\in Y^{-1}(A)$.
Changing the representation changes $Yz$ by $Y(B)\cap A$, so $X$ is
well defined, with kernel $B$ and image $A/C$. Also $Y^{-1}(C)\le B$,
so the hybrid selector accepts $Y$. The two images $Y(B)/C$ and $A/C$
are disjoint; $R=X+(R-X)$ maps onto these components, so $X\preceq R$.

These properties specify the triple uniquely, and no triple exists for
an unselected $Y$. Indeed suppose a triple $C\le A,H\ge B,X$ has those
kernel/image conditions, accepts $Y$ by its hybrid selector, and
$X\preceq q_CY|H$. Then $A\le\operatorname{im}Y$ and $\ker Y\le B$.
Agreement of $R$ with $X$ on $R^{-1}(\operatorname{im}X)$ gives
$Y(B)\cap A\le C$; for $c\in C$, a preimage lies in $H$ and then
in $\ker R\le\ker X=B$, proving the reverse inclusion.
For $Yw\in A$, choose $h\in H$ matching $Yw$ modulo $C$; the hybrid
preimage condition gives $w\in H$. On $Y^{-1}(A)$, $R=X$ and maps
onto $A/C$, whence $H=B+Y^{-1}(A)$. The zero value on $B$ and agreement
on this preimage also determine $X$.
On each character the surviving phase is $\chi_Y(T)$, and the final
frequency is $q_AY|B$. Thus, on the actual common domain,
\[
 R_{A,B,T}P_{A,B}f
   =\sum_{\substack{C\le A,H\ge B\\X:H/B\simeq A/C}}
            D_XD_{C,H,T}f.                            \tag{T1}
\]
The indexing triples are in bijection with linear maps
$\theta:A\to W/B$: take $C=\ker\theta$, $H/B=\operatorname{im}\theta$
and $X$ the inverse induced isomorphism. Conversely invert $X$ and
precompose the quotient of $A$. Hence their number is exactly
$2^{ij}$ for $i=\dim A,j=\operatorname{codim}B$.
Holder's inequality for a sum of $N$ functions costs $N^3$ in fourth
powers. Averaging over the base $T$, whose translation is uniform,
therefore gives
\[
 \|P_{A,B}f\|_4^4\le2^{3ij}
       \sum_{C,H,X}\mathbb E_T\|D_XD_{C,H,T}f\|_4^4.
\]
For nonzero ordinary terms $i,j\le d$. Put
$t=\dim C+\operatorname{codim}H+k$, $k=\operatorname{rank}X$.
Then $i+j=t+k\le2t$, and
$7d(i+j)+3ij\le10d(i+j)\le24dt$.
Each final triple determines the original pair
$A=q_C^{-1}(\operatorname{im}X)$, $B=\ker X$ uniquely. Thus (DR6) gives
\[
 \frac{\|f\|_4^4}{162}\le2^{6d^2}\|f\|_2^4+
  \sum_{C,H,X:t>0}2^{24dt}\mathbb E_T\|D_XD_{C,H,T}f\|_4^4.
                                                               \tag{A6}
\]
Mixed derivatives with $t>d$ are zero by the two rank-lowering formulas.

We next interchange a later hybrid derivative with $D_X$.
Write $A_1=\operatorname{im}X$, $B_1=\ker X$, and fix
$A_1\le A_2$, $B_2\le B_1$. Sum over complements
\[
 A_2=A_1\oplus C,\qquad H+B_1=W,\quad H\cap B_1=B_2,
 \qquad X'=q_CX|H.
\]
Then, with arbitrary actual bases $S,T$,
\[
 D_{A_2/A_1,B_2,T}D_{X,S}f
  =\sum_{C,H}D_{X'}D_{C,H,S+j_{B_1}Tq_{A_1}}f.       \tag{T2}
\]
Here is a proof of both selector directions and uniqueness.
If $X\preceq Y$ passes the left selector, put $Z=Y-X$.
Its image is complementary to $\operatorname{im}X$ and
$\ker X+\ker Z=W$. On $B_1$, the induced $Y$ is the injection of
$Z|B_1$ modulo $A_1$, and $Z(B_1)=\operatorname{im}Z$.
The left hybrid conditions give
$C=\operatorname{im}Z\cap A_2$ complementary to $A_1$, and
$\{w\in B_1:Zw\in C\}\le B_2$, in particular $\ker Y\le B_2$.
Take $H=\ker Z+B_2$. It has the required complement properties.
If $Yw\in C$, disjoint images force $w\in B_1$ and then $w\in B_2$,
so the right hybrid selector holds. On $H=\ker Z+B_2$, the maps $X$
and $Z$ occupy the two complementary components; quotienting by $C$
preserves their disjoint images, proving $X'\preceq q_CY|H$.

Conversely suppose a right selector holds. Since $X(H)=\operatorname{im}X$
and $C\le\operatorname{im}Y$, image inclusion modulo $C$ gives
$\operatorname{im}X\le\operatorname{im}Y$.
If $Yw\in\operatorname{im}X$, choose $h\in H$ with $Yh=Yw$:
the quotient image condition supplies a match modulo $C$, and
$C\le Y(H)$ supplies the correction. Then $w-h\in\ker Y\le H$.
Rank-poset agreement modulo $C$ gives $Yw-Xw\in C\cap A_1=0$.
Thus $X\preceq Y$. Put $Z=Y-X$ again. The hybrid rank drop and
$\operatorname{rank}X'=\operatorname{rank}X=k$ give
\[
 \operatorname{rank}(q_CZ|H)
  =\operatorname{rank}Z-\dim C-\operatorname{codim}H.
\]
For any $Z$, the loss under restriction and quotient is at most this
sum. Equality forces $\ker Z\le H$ and $C\le Z(H)$, hence
$Z^{-1}(C)\le H$. Disjointness from $A_1$ now forces
$C=\operatorname{im}Z\cap A_2$.
Moreover $\ker Z+B_2\le H$ with equal dimensions: their intersection
is $\ker Y$, since $B_2\le\ker X$ and
$\ker Y\le H\cap B_1=B_2$. Rank-nullity gives equality.
This proves uniqueness. It also gives the left hybrid conditions,
since $Z(B_1)=\operatorname{im}Z$ and
$w\in B_1,Zw\in A_2$ implies $w\in H\cap B_1=B_2$.
Finally both sides of (T2) have phase
$\chi_Y(S+j_{B_1}Tq_{A_1})$ and frequency $q_{A_2}Y|B_2$.
This proves the identity without assuming orthogonality of coalescing
frequencies.

We prove simultaneously on all finite spaces, by induction on $d$,
\[
 \|f\|_4^4\le2^{100d^2}Q(f),\qquad
 Q(f)=\sum_{A,B}\mathbb E_T\|D_{A,B,T}f\|_2^4.       \tag{A7}
\]
At $d=0$ only the zero-order derivative survives and equality holds.
In (A6) write the initial pair $(A_0,B_0)$, rank-$k$ map $X$,
$s=\dim A_0+\operatorname{codim}B_0$, and $t=s+k>0$.
The mixed derivative has degree at most $d-t<d$. Apply the induction
hypothesis on its actual smaller space, then (T2) and (A1).
A subsequent hybrid derivative has order $u+v\le d-t$.
The two complement choices in (T2) have counts $2^{ku}$ and $2^{kv}$,
by writing complements as graphs. Their fourth-power cost is at most
$2^{3dk}\le2^{6dk}$. The enlarged ordinary order is
$s+2k+u+v\le d+k$, not necessarily $d$; the count only uses the correct
mixed bound $s+k+u+v\le d$.
With $A_1/A_0=\operatorname{im}X$, $B_1=\ker X$, this yields
\[
 \begin{split}
 \mathbb E_T\|D_XD_{A_0,B_0,T}f\|_4^4
 \le {}&2^{100(d-t)^2+6dk}
 \sum_{\substack{A\ge A_0,B\le B_0\\
                 A\cap A_1=A_0,\ B+B_1=B_0}}
 \mathbb E_T\|D_{X|B\bmod A}D_{A,B,T}f\|_2^4.       \end{split}\tag{A8}
\]
In (A8), the induced quotient is by $A/A_0$ inside $V/A_0$,
with the canonical identification $(V/A_0)/(A/A_0)=V/A$.
Each final $A,B$ reconstructs the intermediate pair as $A+A_1$,
$B\cap B_1$, so there is no further multiplicity at this stage.
For each fixed inner shift, original $T$ plus its canonical embedding
is still uniform on the original group; Fubini removes the inner
average with no cardinality or rank-conditioning factor.

For completeness we count the remaining reindexing. Fix final $A,B,Y$
of dimensions $a=\dim A,b=\operatorname{codim}B,k=\operatorname{rank}Y$;
nonzero terms require $a+b+k\le d$. Fix initial dimensions
$i=\dim A_0,j=\operatorname{codim}B_0$. The exact number of initial
triples inducing $Y$ is
\[
 {a\brack i}_2{b\brack j}_2\,2^{k(a-i)}2^{k(b-j)}.   \tag{A9}
\]
Choose $A_0\le A$ and $B_0\ge B$ first. The image of $X$ is a lift
of $\operatorname{im}Y$ to $V/A_0$ disjoint from $A/A_0$, hence a graph
with $2^{k(a-i)}$ choices. Its kernel in $B_0/\ker Y$ complements
$B/\ker Y$, with $2^{k(b-j)}$ choices. These choices determine $X$
uniquely: project along the chosen kernel, apply $Y$, then lift its
image. This also proves preservation of rank $k$.
The count is at most $2^{d(i+j+k)}$, and we conservatively use
$2^{3d(i+j+k)}$. For $t=i+j+k\in[1,d]$, (A6)--(A9) have exponent
\[
 100(d-t)^2+27dt+6dk
 \le100d^2-73dt+6dk
 \le100d^2-63dt-4dk.                                \tag{A10}
\]
For fixed $k\ge1$, put $z=2^{-63d}$ and sum over $i,j\ge0$:
$z^k/(1-z)^2\le2z^k\le2^{-31d(k+1)}$.
For $k=0$ omit $i=j=0$; then
$(1-z)^{-2}-1\le4z\le2^{-31d}$. Thus
\[
 \begin{split}
 \frac{\|f\|_4^4}{162}\le {}&2^{6d^2}\|f\|_2^4+
 2^{100d^2}\sum_{k=0}^d2^{-31d(k+1)}\\[-2pt]
 &\qquad\cdot\sum_{\substack{A,B,Y:\operatorname{rank}Y=k\\
                             |(A,B)|+k>0}}
 2^{-4dk}\mathbb E_T\|D_YD_{A,B,T}f\|_2^4.          \end{split}\tag{A11}
\]
The coefficients satisfy
$2^{-31d(k+1)-4dk}=2^{-31d-29dk}2^{-6dk}$.
Apply (W6), with the common bound $d$, to each actual $D_{A,B,T}f$,
and enlarge sums by nonnegativity. The last line is at most
$2^{100d^2+1-31d}Q(f)$. Also $\|f\|_2^4\le Q(f)$ by the zero-order
term. For $d\ge1$,
$162(2^{-94d^2}+2^{1-31d})<1$, proving (A7).
This closes a strict-lower-degree induction; its conclusion was not
used at the current degree.

If all influences of a degree-at-most-$d$ function through order $d$
are at most $\eta$, (A7) and (A2) imply
\[
 \|f\|_4^4\le2^{103d^2}\eta\|f\|_2^2.             \tag{A12}
\]
Indeed an input frequency of rank $j$ is selected by exactly
$\sum_{a+b\le j}{j\brack a}_2{j-a\brack b}_2$ hybrid pairs:
choose $A\le\operatorname{im}Y$, then $B\ge Y^{-1}(A)$.
For $j\ge1$ the count is at most
$(j+1)^2 2^{j^2}\le2^{j^2+2j}\le2^{3j^2}$; for $j=0$ it is one.
Replace one factor of each squared influence in $Q(f)$ by $\eta$,
use (A2), and apply this count. Derivatives above the degree vanish.

\subsection{Globalness and both influence conversions}
A function is \emph{up-to-$r$ $\epsilon$-global} if every actual affine
restriction of order at most $r$, at every base, has squared $L_2$ norm
at most $\epsilon$. This definition includes the order-zero norm bound.
We use this nonvacuous definition also when a quotient space has no
restriction of order exactly $r$.

For a line $U=\langle v\rangle\le V$, choose $\phi\in V^*$ uniformly
with $\phi(v)=1$ and $w\in W$ uniformly, independently, and define
$E_Uf(M)=\mathbb E_{\phi,w}f(M+w\phi)$.
On $\chi_Y$, averaging $w$ keeps only $\phi Y=0$.
If $v\in\operatorname{im}Y$ this is impossible; otherwise exactly
$2^{\dim V-\operatorname{rank}Y-1}$ of the $2^{\dim V-1}$ functionals
qualify. Its multiplier is therefore zero on the order-one hybrid
selector and $2^{-\operatorname{rank}Y}$ elsewhere.
For a hyperplane $B\le W$, let $\psi$ be its nonzero defining functional,
choose $w$ uniformly with $\psi(w)=1$ and $\phi$ uniformly in $V^*$.
The same translation average has multiplier
$\Pr[Yw=0]$, which is zero if $\ker Y\le B$ and
$2^{-\operatorname{rank}Y}$ otherwise. These are direct finite counts;
the two distributions remain meaningful in the one-dimensional and
singleton boundary cases whenever the line or hyperplane exists.
For either operator $E$, with its hybrid selector $L$, one has
\[
 L(f^{=j})=f^{=j}-2^jE(f^{=j}).                     \tag{A13}
\]
For $j\ge1$ set
$P_j=(I-2^jE)(I-2^{j-1}E)$.
On both ranks $j,j-1$ it equals $L$. A raw order-one restriction loses
exactly one rank on selected frequencies and zero otherwise. Hence only
those two input ranks can reach output rank $j-1$, and
\[
 (R_{U,T}P_jf)^{=j-1}=D_{U,T}(f^{=j}).              \tag{A14}
\]
The selected rank-zero part is zero when $j=1$; no negative rank is
identified with rank zero. This identity holds for arbitrary $f$ and
every $T$.

Translations preserve globalness at all bases. Minkowski implies the
same for any convex mixture of translations, in particular $E,E^2$.
The coefficient sum of $P_j$ is
$(1+2^j)(1+2^{j-1})\le2^{2j+1}$.
Thus, if $f$ is up-to-$j$ $\epsilon$-global, the actual witness
$f'=R_{U,T}P_jf$ is up-to-$(j-1)$
$4\,2^{4j}\epsilon$-global and has level $j-1$ given by (A14).
Indeed composing a further restriction with $R_{U,T}$ adds one to its
order and adds its canonical embedded base to $T$, preserving the
normalized measure. This works for both a domain line and codomain
hyperplane, and uses the requested base $T$, not only zero.

For a derivative of order $k\le d$, peel off a line in its nonzero
domain constraint, or otherwise a hyperplane containing its codomain
constraint. Apply this witness at the first base $T$ and subsequently
at zero. Formula (A1) preserves the specified total base. After $k$
steps, Parseval for the remaining level gives
\[
 I_{A,B,T}(f^{=d})
 \le2^{4kd-2k^2+4k}\epsilon
 \le2^{10d^2}\epsilon.                            \tag{A15}
\]
Here $f$ was up-to-$d$ global but had no degree assumption.
The product of losses is
$\prod_{j=d-k+1}^d4\,2^{4j}$; its exponent is at most $2d^2+4d$
for $d\ge1$. At $k=0$ use the whole-space Fourier projection bound,
and at $d=0$ this is the only case. Thus all orders, not just order $d$,
are covered. For a full degree-at-most-$d$ function, the images of its
levels under a fixed hybrid derivative are orthogonal, having distinct
ranks $i-k$. Applying (A15) to each level and summing gives
\[
 I_{A,B,T}(f)\le2^{11d^2}\epsilon\quad(k\le d),       \tag{A16}
\]
since $(d+1)2^{10d^2}\le2^{11d^2}$ for $d\ge1$.
The $d=0$ assertion is direct. This uses orthogonality between levels,
not between colliding individual frequencies.

We also prove the reverse implication: if a degree-at-most-$d$ function
has all influences through order $d$ at most $\epsilon$, then for every
natural $r$ it is up-to-$r$ $2^{10dr}\epsilon$-global. First note that
level projections inherit the influence bound, because they are
orthogonal projections of the actual reduced derivative. Order-one
derivatives inherit all influences through $d-1$ by (A1).

The only additional measure calculation is the following. Suppose $f$
is up-to-$s$ $\eta$-global. Restrict $E_Uf$ first at a line $U=\langle v\rangle$
and then at further order at most $s$. Write the parent variation as
$R\in\mathcal H(V/A,B)$ with $U\le A$ and
$\dim A+\operatorname{codim}B\le s+1$.
Jensen bounds its squared norm by
$\mathbb E_{R,\phi,w}|f(M_0+R+w\phi)|^2$.
Condition on $A'=\ker(\phi|A)$ and $B'=B+\langle w\rangle$.
The restriction of $\phi$ to $A$ is fixed by $A'$ and $\phi(v)=1$;
outside $A$ its coordinates remain independently uniform.
In coordinates on $V/A'$ starting with $v$, $R$ has first column zero
and other columns independently uniform in $B$.
If $B'=B$, $w$ is uniform in $B$, and the sum is uniform on
$\mathcal H(V/A',B)$. If $\dim B'=\dim B+1$, $w$ is uniform in
$B'\setminus B$; every other column is an independent uniform element
of $B$ plus an independent uniform bit times $w$, hence uniform in $B'$.
Thus the resulting map is uniform conditional on its $v$-column being
outside $B$, an event of density exactly $1/2$.
The unconditional restriction orders are at most $s$ and $s-1$,
respectively. Nonnegative expectation under this conditioning costs
at most two, so the desired squared norm is at most $2\eta$.
When $s=0$ the expanded case is impossible ($B=W$), so no negative-order
hypothesis is used. Arbitrary bases are absorbed by translation.
Codomain hyperplanes follow by transposing the spaces: restrictions
$(A,B)$ become $(B^\perp,A^\perp)$ with the same order and uniform law.

For homogeneous $f$ of degree $d\ge1$, (A13) reads
$f=L_Uf+2^dE_Uf$. If $f$ is global through $r-1$ with parameter $\eta_2$
and every order-one derivative is global through $r-1$ with parameter
$\eta_1$, the preceding calculation and squared triangle inequality
bound each order-$r$ restriction by
\[
 2\eta_1+4\,2^{2d}\eta_2.                          \tag{A17}
\]
Induct first on $d$ simultaneously for all spaces and all $r$, then on
$r$. The $d=0$ and $r=0$ cases follow from order-zero influence.
For $d,r\ge1$ split into rank levels. Lower levels have global bounds
$2^{10ri}\epsilon$ by outer induction. The top level has the
$r-1$ bound $2^{10d(r-1)}\epsilon$ by inner induction, and its
order-one derivatives have the bound
$2^{10(d-1)(r-1)}\epsilon$ by outer induction.
Relative to $K=2^{10dr}\epsilon$, (A17) costs at most
\[
 2\,2^{-10(r+d-1)}+4\,2^{-8d}\le9/512<1/4.
\]
Smaller-order top restrictions already satisfy the same $K/4$ bound.
For all lower levels together the squared triangle and geometric bound
is at most
$\epsilon(\sum_{i<d}2^{5ri})^2\le K/961$.
Combining the top and lower sums costs at most
$K/2+2K/961<K$. This proves
\[
 \text{influences through $d$}\le\epsilon
 \quad\Longrightarrow\quad
 \text{globalness through $r$}\le2^{10dr}\epsilon
 \quad\text{for all }r\ge0.                       \tag{A18}
\]
If exact-order-$r$ restrictions do not exist, use the smaller-order
induction result, not a choice from an empty family. If a level is
unavailable it is zero. The case $\epsilon=0$ follows directly from
order-zero norm, without division.

\subsection{Square-globalness and all dyadic moments}
Suppose $f$ has degree at most $d$ and is up-to-$d$
$\epsilon$-global. Combining (A16) with (A12) gives
\[
 \|f\|_4^4\le2^{114d^2}\epsilon\|f\|_2^2.           \tag{A19}
\]
Combining (A16) with (A18) at $r=3d$ gives up-to-$3d$ globalness
parameter $B=2^{41d^2}\epsilon$.
Every raw restriction $h$ of order at most $2d$ still has degree at most
$d$ and is up-to-$d$ $B$-global, by composition of restrictions.
Applying (A16) and (A12) on its actual quotient/subspace space yields
\[
 \|h\|_4^4\le2^{114d^2}B\|h\|_2^2
              \le2^{196d^2}\epsilon^2.              \tag{A20}
\]
Both factors $B$ are required. Since raw restriction commutes with
squaring and $\deg(f^2)\le2d$, the actual square is up-to-$2d$ global
with parameter $2^{196d^2}\epsilon^2$.

For every dyadic $p\ge2$ we claim
\[
 \|f\|_p^p\le2^{200d^2p^2}\|f\|_2^2
                         \epsilon^{p/2-1}.         \tag{A21}
\]
At $p=2$ the last factor is one. If $\epsilon=0$ then $f=0$; if $d=0$
then $f=c$ is constant and $|c|^2\le\epsilon$, proving the claim
without loss. For $d\ge1$, $\epsilon>0$, start at $p=4$ with (A19).
Define $A_4=114$ and $A_p=4A_{p/2}+49p-82$ for $p\ge8$.
Inductively apply the stronger moment bound with exponent $A_{p/2}$
to $g=f^2$, its actual degree bound $2d$, and the parameter from (A20).
Using $\|g\|_2^2=\|f\|_4^4$ and (A19), the total exponent is
\[
 4A_{p/2}+196(p/4-1)+114=4A_{p/2}+49p-82,
\]
and the density power is $2(p/4-1)+1=p/2-1$.
The factor four retains the doubled degree. The invariant
$A_p\le200p^2-100p$ holds at $p=4$ and propagates because
$4(200(p/2)^2-100(p/2))+49p-82=200p^2-151p-82$.
This proves (A21) for $2,4,8,\ldots$ on all finite dimensions.
No exact-order globalness is inferred on an undersized quotient, and
no dyadic theorem was imported to prove (A21).

\subsection{The $L^{p'}$ level bridge and the Boolean conclusion}
Let $p\ge2$ be dyadic and $p'=p/(p-1)$. For arbitrary $f$, suppose every
restriction through order $i$ has $L^{p'}$ norm at most $\epsilon$.
This is a norm, not a squared norm. We prove
\[
 I_{A,B,T}(f^{=i})\le2^{500i^2p}\epsilon^2
 \quad\text{for }|(A,B)|\le i.                     \tag{A22}
\]
For $p=2$ use (A15). For $p\ge4$ the following duality estimate will be
used only after its influence premise has been established.
Put $h=f^{=j}$, $E=\|h\|_2^2>0$, and suppose all its influences through
$j$ are at most $\beta E$ (necessarily $\beta\ge1$).
By (A18) its globalness parameter is $2^{10j^2}\beta E$.
Taking the $p$th root in (A21) gives
\[
 \|h\|_p\le2^{210j^2p}\beta^{1/2-1/p}\sqrt E.
\]
Since the actual orthogonal projection has $|\langle h,f\rangle|=E$,
Holder and division by $\sqrt E$ give
\[
 E\le2^{420j^2p}\beta^{1-2/p}\|f\|_{p'}^2.          \tag{A23}
\]
The zero-energy case is direct.

Induct on $j$ for (A22), simultaneously on all finite spaces.
At $j=0$ the level is constant and Holder gives $|\mathbb Ef|\le\epsilon$.
The translation mixtures $E_U,E_U^2$ also preserve globalness in
$L^{p'}$ by Minkowski. The polynomial in (A14) has coefficient sum at
most $2^{3j}$ for $j\ge1$. Thus its explicit witness at every base is
up-to-$(j-1)$ global in $L^{p'}$ with parameter $2^{3j}\epsilon$.
The inductive hypothesis and (A14) bound every positive-order influence
of $f^{=j}$ by
\[
 B=2^{500(j-1)^2p+6j}\epsilon^2.
\]
All positive orders factor through an order-one derivative as in
(A15), so none is omitted. Let $E=\|f^{=j}\|_2^2$.
If $E\le B$, every influence is at most $B$, which is at most the bound
in (A22) since $6j\le500(2j-1)p$.
If $E>B$, the proved positive-order bounds and the exact zero-order
energy show that every influence is at most $E$. Only now apply (A23)
with $\beta=1$, obtaining $E\le2^{420j^2p}\epsilon^2$ and hence (A22).
There is no assumption of the desired influence bound in this case
split, and (A21) was proved without using this bridge.

\begin{proof}[Proof of Theorem~\ref{thm:binary-hc}]
Every actual affine restriction $T+\mathcal H(\mathbb F_2^D/A,B)$ of
order at most $i\le r$ is a solution set of vector equations:
choose a basis of $A$ to fix $M$ on it as $T$ does, and quotient rows
for $B$ to impose the codomain constraints. Pad with zero-equals-zero
equations to make the nominal budget $r$. Neither the solution set nor
its uniform measure changes. Thus all these restrictions have density
at most $\delta$, including the padded empty restriction, which gives
$\mathbb EF\le\delta$.
For a Boolean function, its $L^{p'}$ norm on a restriction of density
$a$ is $a^{1/p'}$. Apply (A22) with
$\epsilon=\delta^{1-1/p}$ to $h=F^{=i}$. For $i\ge1$, $\delta>0$ its
influence parameter is
$\eta=2^{500i^2p}\delta^{2-2/p}$.
By (A18) its up-to-$i$ squared-$L_2$ globalness parameter is
$\eta_1=2^{(10+500p)i^2}\delta^{2-2/p}$.
Apply (A21) and use Parseval and Booleanity:
$\|h\|_2^2\le\|F\|_2^2=\mathbb EF\le\delta$. Hence
\[
 \begin{split}
 \|h\|_p^p
 &\le2^{(450p^2-495p-10)i^2}\delta^{p-2+2/p}\\
 &\le2^{500i^2p^2}\delta^{p-2}.
 \end{split}
\]
The calculations are
$200p^2+(10+500p)(p/2-1)=450p^2-495p-10$ and
$1+(2-2/p)(p/2-1)=p-2+2/p$.
The last inequality uses $0<\delta\le1$ in the correct direction.
Take the $p$th root. If $\delta=0$, the padded empty restriction forces
$F=0$. At $i=0$, the projection is the constant
$\mathbb EF\le\delta\le\delta^{1-2/p}$; unavailable ranks give zero.
These cases also cover zero-dimensional matrices.
\end{proof}

If one instead starts with independent restrictions of order exactly
$i$, an up-to-$i$ bound follows when $i\le\dim V+\dim W$ by partitioning
each lower-order affine variation space into cosets of a chosen
order-$i$ variation subspace and averaging the relevant norm powers.
For a rank-$i$ conclusion, larger $i$ gives the zero level directly.
For a full bounded-degree function, a vacuous exact-order premise does
\emph{not} give globalness; all full-function uses above explicitly
assume up-to-order bounds. The nominal-budget hypothesis of
Theorem~\ref{thm:binary-hc} avoids this issue by zero padding.
In Lemma~\ref{lem:inverse-explicit} take $\delta=2e\le1$ and the
stated dyadic moment. Probability-norm monotonicity supplies any smaller
moment used there. This discharges precisely the binary analytic input,
without changing the remaining upstream contracts of the manuscript.
```
