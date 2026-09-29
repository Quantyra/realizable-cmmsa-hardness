# Core Theorem 1 external-contract source audit (2026-09-29)

This note checks the *scope* of cited inputs for a conditional Lean certificate.
The citations remain **external mathematical contracts**. A Lean structure field
or theorem parameter records an assumption; it does not prove the cited result.
No source result below supplies the changed-ambient `8S` application or the
complete source-to-CMMSA map.

## MZ outer 3-Lin hardness and smooth game

[MZ arXiv v1, Definition 3.1, Theorem 3.1, Section 3.2 and Claim 3.2](https://arxiv.org/pdf/2510.23991v1)
define 3-Lin with exactly three variables per row, at most ten rows per
variable, and at most one shared variable between distinct rows. There is one
absolute `s₀<1` such that **for every fixed positive** outer YES error `ε₁`,
`Gap3Lin[1−ε₁,s₀]` is NP-hard. Write `η=1−s₀>0`; `η` and the soundness
constant do not depend on the later `ε₁`.

For a fixed 3-Lin instance and parameters `0≤β<1`, advice length `r`, and
repetition count `J`, the game independently samples `J` equations. In each
row it retains all three coordinates with probability `1−β`, otherwise one
uniform coordinate. It draws `r` independent advice vectors on the retained
coordinates and extends them by zero to the first prover's question. The
provers answer assignments; the verifier checks agreement on retained
coordinates and satisfaction of all `J` equations. Claim 3.2 gives honest
success at least `1−J ε₁` when the 3-Lin value is at least `1−ε₁`, and game
value at most `2^{−Ω(η² 2^{−r} βJ)}` when its value is at most `s₀`.

**Lean contract boundary:** an external contract must range over an encoded
bounded-occurrence 3-Lin source reduction and the *actual* smooth game
strategy/value law, with one `s₀,κ` chosen before all later positive `ε₁`.
`ActualMZOuterSourceContract` now types an indexed product-game law, its
strategy value bound, and an encoded SAT-to-outer `SeededMap` as **external
fields**. No inhabitant, fixed encoding implementation, or bridge from the
manuscript decoder's actual observation is proved. A broad source-to-CMMSA
`Preserves` premise would absorb the manuscript's new comparison and is not
a cited result. The main MZ PCP theorem chooses alphabet after its positive
errors, so it cannot supply the manuscript's inverse-alphabet late `ε₁`
choice by itself.

## MZ star transport and scoped decoder

[MZ Section 3.3, Lemmas 3.3–3.4](https://arxiv.org/pdf/2510.23991v1)
give the leaf-vertex clique equivalence and the *unique* transport of a
linear label that respects the equation side conditions at both vertices.
The source samples fixed legitimate first questions, a transverse center,
independent transverse leaves, then representatives from leaf classes. The
external transport claim must retain this actual law and the side conditions;
it does not itself establish the arbitrary-fixed-table collision comparison.

[MZ Theorem 4.2](https://arxiv.org/pdf/2510.23991v1) fixes a first question
`U` and uses the source transverse test law. For fixed `δ>0` and sufficiently
large integral `ℓ`, if side-condition-respecting tables pass with density at
least `S=2^{−2(1−1000δ)ℓk}`, there are `r₁,r₂` with
`r₁+r₂≤10k/δ` such that at least `2^{−6ℓ²}` of the uniform
`r₁`-subspaces `Q` admit a codimension-`r₂` `W⊇Q+H_U` and a linear
side-condition-respecting `g` with conditioned Grassmann agreement at least
`2^{−2(1−1000δ²)ℓ}/5`. Here the manuscript substitutes `k=m, ℓ=h,
δ=ρ`. **External only at this source scope.** The changed-ambient robust
`8S` use, its query-law comparison, and subsequent strategy extraction remain
manuscript-new Lean obligations.

## HN weighted star compilation

[HN revision 1, Definition 4.4 and Lemma 4.6](https://eccc.weizmann.ac.il/report/2026/052/revision/1/download/)
start with a finite star-projection `(m+1)`-CSP with distinct center/leaf
sides, alphabets at most `R`, an edge distribution, and projections from
each leaf alphabet to the center. The construction discards zero-occurrence
vertices, sets
`λ(u)=E_e[1[y=u]+Σᵢ1[xᵢ=u]]/(m+1)`, `Λ=Σᵤλ(u)|Σᵤ|`,
variable weight `λ(u)/Λ`, and budget `s=1/Λ`. For repeated leaf variable
`x`, its branch labels must satisfy **every** projection at occurrences of
`x`. Lemma 4.6 supplies a polynomial-time local formula construction,
monotonicity and leaf size at most `(m+1)R`; for **every** `τ∈[0,1]`, CSP
value at least `1−τ` gives a formula-distribution assignment of weight `s`
satisfying at least `1−τ`; and if CSP value is at most `ζ`, every assignment
of weight at most
`(1/8)(5/8)^{1/(m+1)} ζ^{−1/(m+1)}s` satisfies at most `3/4`.

**Lean contract boundary:** source compilation stops at the weighted base
formula distribution. It gives neither an AND product nor dyadic
approximation, empirical list, exact-YES repair, rational common-denominator
rounding, or encoded FP output. HN Theorem 4.5 supplies its star PCP hardness
only with the alphabet threshold selected *after* both positive errors. The
manuscript's `σ=⌊R^{1−1/m}/16⌋` is a later conservative specialization of
Lemma 4.6 after `ζ=R^{−(1−1/m²)m}`; that numeric implication must be proved
in Lean rather than treated as part of the cited compiler. The existing
`StarFormulaInterface` and `StarCmmsaSemantics` prove substantial finite
semantic pieces locally, but do not constitute an encoded general compiler.

## Current Lean status and remaining conditional dependencies

`ActualTheorem1ExternalContracts.ExternalMZ24MaximalPairCount` is an explicit
external structure over actual Grassmann tables and maximal-pair predicates;
its checked projection has only standard Lean axioms. Its coarse
`B^{−2}2^{C h}` source bound still needs an explicit Lean derivation from
the source's constant to be called a source-exact contract. No typed outer
game, source-scoped decoder, or general encoded HN compiler inhabitant has
been supplied. The independent changed-ambient `8S` decoder, outer strategy,
late-error YES reduction, and finite-list/encoding composition remain
conditional manuscript-new dependencies. Thus the core Theorem 1 certificate
is not yet complete and no numeric NO-soundness gap has been closed by this
source audit.
