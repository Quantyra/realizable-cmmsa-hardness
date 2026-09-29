# MZ outer game: first missing semantic quotient

Source: [MZ arXiv v1, Section 3.2 and Claim 3.2](https://arxiv.org/pdf/2510.23991v1), PDF lines 471–545.

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
