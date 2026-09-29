# MZ outer game: first missing semantic quotient

Sources: [MZ arXiv v1, Section 3.2 and Claim 3.2](https://arxiv.org/pdf/2510.23991v1),
PDF lines 471–545; [MZ24, Section 3.1.4 and Claim 3.2](https://eccc.weizmann.ac.il/report/2024/027/download/),
PDF pages 16–17. MZ24 explicitly defines the game as the parallel repetition of
the one-row smooth game and samples every row coordinate independently. It uses
the same union/concatenation notation as MZ25.

Definition 3.1 requires three distinct variables per row, degree at most ten,
and overlap of at most one variable for distinct rows. `Finite3LinSource`
already provides the first condition through `row_injective`; a separate
predicate must enforce the latter two for a source-scoped contract.

The verifier independently samples `J` equations; each row retains all three
variables with probability `1−β`, otherwise one uniformly selected variable.
It samples `r` independent uniform advice vectors on each retained row, and
extends each by zero for the first question. The first prover sees the equation
tuple and extended advice. The second sees retained `V` and its advice. The
verifier checks agreement on retained variables and every sampled equation.

**Exact missing semantic statement.** Section 3.2 writes `V=⋃ᵢVᵢ` while
also writing each advice vector as the concatenation `(vᵢⱼ)ᵢ`. If sampled rows
overlap, independently sampled bits for the same variable can disagree, so
the concatenation is not automatically a function on the set union `V`.
The repository needs a typed source question space and a map from the
independent row-wise sample to that space that specifies this collision case.
Only then can Claim 3.2 be an external contract over the *same* strategy
value as the manuscript decoder. A tagged row-wise second question may reveal
extra information and cannot be substituted silently.

MZ24 narrows the natural interpretation: the **product-game** second question
has indexed coordinate sets `(Vᵢ)ᵢ` and advice functions on the occurrence
type `{(i,x) | x∈Vᵢ}`. Its assignment is also indexed by occurrences. This is
exactly the usual parallel-repetition game to which its Claim 3.2 proof
applies. Writing that occurrence type as a literal set union would silently
identify `(i,x)` and `(j,x)` and can make independently sampled advice
inconsistent. Conversely, treating the full indexed question as the source
question may give the second prover more information than a literal union
question. The papers' prose does not settle this identification.

**First missing theorem for the manuscript decoder.** Define the product-game
value on the independent occurrence sample, and define the actual decoded
strategy's observation and acceptance event. Prove a success-preserving
strategy map from **every** decoder-produced strategy on the actual observation
to a strategy for that exact product game, for all encoded NO instances and all
fixed tables. If the decoder is evaluated only on legitimate disjoint rows,
prove the event-law identity on that restriction and the sharp inequality
`Pr[win | legitimate] ≤ val(product game)/Pr[legitimate]`. This inequality
requires `Pr[legitimate]>0` and follows by extending the strategy arbitrarily
outside the event; it is not a consequence of merely naming both games
"tagged." The same map must preserve the real-valued lower bound
`2^(-10h²)` from the decoder and the outer upper bound
`2^(-κ A h²)` after the legitimate-event loss. Here the absolute `κ>0` is
fixed from the source soundness theorem before the later arbitrary positive
YES error `ε₁`; `A` is then chosen with `20<κ A` before `h`.

One possible route is to restrict to the manuscript's legitimate disjoint-row
event, prove equality of its conditioned question law with the source game
conditioned on that event, and prove the exact conditioning loss
`success_cond ≤ success_source / Pr[legitimate]`. The source's Claim 3.2
upper bound then applies with its absolute `κ>0` chosen before advice length,
repetition count, and every later outer YES error. This route still requires
the encoded bounded-occurrence Gap3Lin reduction of Theorem 3.1, with one
absolute `s<1` chosen before every positive outer YES error. Neither result is
provided by `Finite3LinSource` or the present source audit.

No Lean claim over a tagged proxy was retained. This audit does not reduce
the numeric NO-soundness gap.
