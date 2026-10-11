# Adaptive refresh, progress, termination, and distinct-Q argument

Status: mathematical argument offer for E002/S3137; source-level assessment only. No Lean translation, compilation, GCP run, final decoder, source-NO implication, or independent review is claimed.

## Pinned statement and scope

The canonical statement is the lemma “Robust enlarged-ambient local application” in paper/submission-manuscript.md, SHA-256 16E77E937685F55BA96CD276BBDE4E65EF36F25C25B790E946F5E3EC9CFAA449, beginning at manuscript line 754. Its parameters are fixed before the argument: \(m\ge2\), \(0<\rho\le1/4000\), integral \(r=10m/\rho\), \(d=2h\), \(t=2(1-\rho)h\),

\[
S=2^{-2(1-1000\rho)hm},\qquad e=2^{-2(1-1000\rho^2)h},\qquad C=e/5.
\]

Fix the ambient \(n=2J\), a side complement of dimension \(2J\), its coordinate equivalence, and arbitrary center and leaf tables once. The center table stays fixed. The leaf table has one dual label \(T(L)\in L^*=\operatorname{Hom}(L,\mathbb F_2)\) for each distinct \(d\)-space \(L\). The ordinary star law samples a uniform center \(K\), then \(m\) independent uniform \(d\)-spaces containing \(K\). At every refresh step, conditional on the entire past, redraw every label indexed by the current union \(X\), independently and uniformly from its actual \(L^*\); leave labels outside \(X\) unchanged. This conditional product law is essential. Refreshing only newly added entries would not justify the conditional Chernoff bound below.

The local inverse premise used here is the one-inverse statement: whenever the current ordinary star density is at least \(S\), it returns a nonempty zoom and linear \(g\) agreeing with the current leaf table on a fraction greater than \(e\). The star density premise includes the fixed center table. The fixed-coordinate candidate is still uncompiled. Thus the argument below is conditional on that mathematical interface and the exact density transport into the chosen complement.

## One-step preservation under adaptive history

Let \(X\subseteq\mathrm{Grass}(V,d)\) be fixed by a history before a refresh. Consider every candidate \(Q\subseteq W'\subseteq V\), with \(\dim Q+\operatorname{codim}W'=r\), and every linear \(g:W'\to\mathbb F_2\). This entire finite candidate universe is fixed independently of the newly sampled labels; it includes any candidate the inverse may choose after seeing those labels.

For a fixed candidate, let
\[
Z=X\cap\operatorname{Zoom}[Q,W'],\qquad M=|Z|.
\]
For each distinct \(L\in Z\), the new \(T(L)\) is uniform on \(L^*\). Restriction \(g|_L\) is one fixed member of \(L^*\), so
\[
\Pr[T(L)=g|_L\mid\text{entire prior history}]=2^{-d}=2^{-2h}=:p.
\]
The indicators for distinct \(L\) are conditionally independent. If \(X\) has relative zoom measure below \(2^{-2h}\), at most this fraction of all zoom entries can contribute agreement using refreshed labels. Otherwise, on the preservation event, at most \(2^{1-2h}=2p\) of the zoom entries in \(X\) have their refreshed label equal to \(g|_L\). In either case, the new-table agreement contributed by entries in \(X\) is at most \(2^{1-2h}\) of the zoom. Consequently, if the inverse is applied after this event and returns agreement greater than \(e\), then more than \(e-2^{1-2h}\ge e/2\) of that agreement comes from entries outside \(X\), where the current table still equals the original leaf table. This uses \(2^{1-2h}\le e/2\). The comparison concerns leaf-table agreement only; the inverse theorem does not claim that \(g\) agrees with the center table.

For the second case, the manuscript’s Gaussian estimate gives
\[
M\ge 2^{-2h}2^{(2h-r)(n-r-2h)}.
\]
The mean number of refreshed labels matching \(g\) is \(pM\), and the bad event has more than \(2pM\) matches. Chernoff gives
\[
\Pr[\text{bad for this }(Q,W',g)\mid\text{history}]
\le \exp(-pM/3)
\le \exp(-2^E/12),
\quad E=-4h+2+(2h-r)(n-r-2h).
\]
The last inequality uses \(pM\ge2^{E-2}\). The number of candidates is at most
\[
16(r+1)^2 2^{n(r+1)}:
\]
there are at most \(4\cdot2^{an}\) \(a\)-spaces and \(4\cdot2^{cn}\) codimension-\(c\) spaces for each \(a+c=r\), at most \(2^n\) linear functions on each \(W'\), and at most \((r+1)^2\) dimension choices. A union bound, conditional on any past history, therefore gives exactly
\[
F_n=16(r+1)^2 2^{n(r+1)}\exp(-2^E/12).
\]
This union bound over the whole universe handles adaptively selected inverse outputs. No independence between the output candidate and the refreshed labels is assumed.

The probability \(2^{-2h}\) above is the actual dual-label probability, not a heuristic ambient-function probability: each distinct refreshed leaf domain has dimension \(2h\), and its label is independently uniform in that domain’s dual. If the source label is expressed as a functional on \(H+L\) constrained to take prescribed values on \(H\), restriction to \(L\) is an affine bijection onto \(L^*\); uniform constrained labels induce the same uniform dual law. In the fixed-complement coordinates used by this argument, the labels are directly elements of \(L^*\).

## Progress and termination

Initialize \(X_0=\varnothing\) and let the current leaf table initially equal the original table. At stage \(i\), apply the inverse to the current table if its star density is at least \(\epsilon_A/2\). It returns a zoom with agreement greater than \(e\). For \(i=0\), every entry is still original. For \(i>0\), the successful preservation event from the preceding refresh applies to every possible candidate, including the inverse’s adaptive output; it bounds the agreement contributed by entries in \(X_i\) by \(2^{1-2h}\). Thus more than \(e/2\) of the selected zoom agrees with the original table on entries outside \(X_i\). Add the zoom’s \(d\)-spaces to form \(X_{i+1}\), then refresh every label in this enlarged set. The one-step Chernoff/union bound applies conditionally at this refresh and supplies the preservation event needed at the next stage. The zoom’s measure among all \(d\)-spaces is at least \(2^{-rn}/4\) under the stated dimension bounds. Thus each successful inverse step increases the uniform mass of the union by at least
\[
\Delta=e\,2^{-rn}/8.
\]
Since \(\mu(X)\le1\), no path on which every preservation event succeeds can make more than
\[
B_n=\left\lceil 8\,2^{rn}/e\right\rceil+1
\]
steps. This is a potential argument and does not assume the star density decreases monotonically at each refresh.

Cap the recursion at \(B_n\) refreshes, abort on the first failed preservation event, and pad stopped or aborted paths with absorbing states through this fixed horizon. At each active refresh, conditional failure probability is at most \(F_n\), so the sequential union bound gives probability at least \(1-B_nF_n\) that every reached event succeeds. If \(B_nF_n<1/2\), such a history exists. On a no-failure path, the potential bound forces termination by the horizon: otherwise another inverse step would be possible, and its preceding preservation event would force another increase of at least \(\Delta\), exceeding the total mass budget.

At termination, the density has dropped from \(\epsilon_A\) to below \(\epsilon_A/2\). The initial and final acceptance indicators can differ only if at least one of the \(m\) leaf occurrences lies in \(X\). Under the ordinary star law, each occurrence has uniform marginal on all \(d\)-spaces. Write \(N_t=\left[\begin{smallmatrix}n\\t\end{smallmatrix}\right]_2\), \(N_d=\left[\begin{smallmatrix}n\\d\end{smallmatrix}\right]_2\), \(E=\left[\begin{smallmatrix}n-t\\d-t\end{smallmatrix}\right]_2\), and \(M=\left[\begin{smallmatrix}d\\t\end{smallmatrix}\right]_2\). Double-counting incident pairs \(K\subseteq L\) gives \(N_tE=N_dM\). A fixed \(L\) is therefore the \(i\)-th leaf with probability \(M/(N_tE)=1/N_d\); the other leaf factors sum to one. This requires \(t\le d\le n\), which holds under the selected dimension cutoffs. Repeated occurrences do not alter the union bound:
\[
|\epsilon_A-\epsilon_{\rm final}|
\le \Pr[\exists i:L_i\in X]
\le\sum_{i=1}^m\Pr[L_i\in X]
=m\mu(X).
\]
Consequently \(\mu(X)>\epsilon_A/(2m)\). This conclusion uses only bounded acceptance change and uniform leaf marginals; it does not require independence among leaves after conditioning on their common center.

## Counting distinct advice spaces

For every selected inverse output, record its \(Q\), its selected zoom, and its dimensions. Keep only distinct \(Q\)’s, and for each such \(Q\) select one successful visit and one witnessing pair \((W',c)\). Repeated visits to the same \(Q\), even with other zooms or other \(W'\), are counted once. If \(L\in X\), it belongs to a selected zoom, hence contains at least one of these recorded \(Q\)’s. Therefore
\[
\mu(X)\le \sum_{a,c}N_{a,c}\,2^{4h^2-an},
\]
where \(N_{a,c}\) counts assigned distinct \(a\)-spaces with assigned codimension \(c\). For one \(Q\), the fraction of all \(d\)-spaces containing it is at most \(2^{4h^2-an}\), by the Gaussian-binomial ratio and \(a,c\le r\) under the selected \(h\)-cutoffs. This is a union bound over the distinct \(Q\)’s; counting algorithmic visits here would be invalid because repetitions do not describe new covered spaces.

Let \(T_a\) be the number of all \(a\)-spaces in the fixed complement and \(f_{a,c}=N_{a,c}/T_a\). The bound \(T_a\le4\cdot2^{an}\) yields
\[
\sum_{a,c}f_{a,c}\ge \epsilon_A 2^{-4h^2}/(8m).
\]
If the mean initial ordinary density over complements is at least \(8S\), complements with \(\epsilon_A\ge4S\) have mass at least \(4S\): since every density is at most one, the mean is at most \(4S\) plus the mass of that set. Average the fractions over all complements, assigning zero to bad complements. On each good complement the summed fraction is at least \(4S\,2^{-4h^2}/(8m)\), so the total summed averaged mass is at least \(2S^2 2^{-4h^2}/m\). Pigeonholing over at most \((r+1)^2\) dimension pairs fixes one pair \((a,c)\), with success probability at least
\[
\frac{2S^2}{m(r+1)^2}2^{-4h^2},
\]
and hence at least the manuscript’s weaker \(2S^2 2^{-4h^2}/(m(r+1)^3)\). This is an unconditional marginal over the fixed-complement experiment: successful complements form a subset, and no conditioning on success is applied to the \(Q\)-law. Any later conversion to a uniform \(Q\) in the enlarged ambient incurs its separate stated correction \(2^{a+1-2J}\); it is not part of this counting step.

## Selected-parameter cutoff check

For the existing selector, put \(b=4000m^2\), \(\rho=1/b\), \(r=10mb\), \(n=2J\), and \(e=2^{-2(1-1000\rho^2)h}\). The selected numeric height gives \(h\ge b^2\), \(h\ge8(r+1)\), and \(n\ge8h+4r+16\). These imply \(2^{1-2h}\le e/2\), \(E\ge hn/2\), and
\[
B_n\le2^{rn+2h+4},\qquad
16(r+1)^2 2^{n(r+1)}\le2^{n(r+1)+2r+4}.
\]
Write \(K=n(2r+1)+2h+2r+8\), the sum of the two base-two exponents. With \(x=hn\), the selected bounds give \(K+1\le3x\), while \(2^E/12\ge2^{x/2}/12>3x\) in this regime. Thus
\[
\log(B_nF_n)\le K\ln2-2^E/12<-1,
\]
so \(B_nF_n<e^{-1}<1/2\). These are explicit arithmetic consequences of the pinned selected height, not a proof of a refresh history or a translation result. The existing robust-cutoff candidate records dimension guards only; it explicitly does not formalize the Real \(B_nF_n\) inequality.

## Fixed-frame and source-law obligations

One coordinate equivalence for the chosen complement must be selected before the initial density and kept fixed throughout the recursion. The full star event transports by direct restriction naturality: for \(K\subseteq L\), the center label and leaf label restrict along the same induced equivalence, so their equality on the center is preserved for every leaf occurrence. The existing matching-functional coordinate iff is insufficient because arbitrary or refreshed leaf labels need not extend to one common ambient functional. The product of induced dual-space bijections preserves the independent uniform refresh law. The candidate fixed-coordinate inverse is arbitrary-table generic but uncompiled.

To enter the complement argument from the manuscript’s actual test, separately establish: (i) the fixed-\(U\) canonical density equals the same-\(U\) side-conditioned density; (ii) averaging over complements gives the required ordinary density lower bound using the source-to-ordinary acceptance inclusion; (iii) the actual star law has uniform leaf marginals, including repeated occurrences; and (iv) the direct-sum extension from \(W'\) to \(W'+H\) preserves the agreement event for the original row-respecting table. These are transport premises, not consequences of the Chernoff bound or counting argument. The fixed-frame assessment identifies the required interfaces and the missing bundled proofs.

This argument proves only the adaptive refresh preservation, potential growth, termination, and distinct-\(Q\) counting steps conditional on the stated one-inverse and density-transport interfaces. It assumes no final decoder, source-NO theorem, or many-\(Q\) conclusion. It does not close the full manuscript route.
