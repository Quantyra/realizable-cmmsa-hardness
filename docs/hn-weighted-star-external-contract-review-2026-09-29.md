# HN weighted-star external contract: bounded closeout (2026-09-29)

`ActualCoreSourceContractScopes.lean` records HN revision 1, Definition 4.4 and
Lemma 4.6 as an **external** theorem parameter over every finite star satisfying
its typed source preconditions. Those preconditions include `m ≥ 1`, a global
center/leaf partition, positive occurrence weight for every listed vertex
after zero-occurrence deletion, normalized edge weights, and alphabet cap.
The conclusion uses the repository's actual repeated-leaf-consistent formula
compiler and occurrence weights. It states the `(m+1)R` leaf bound,
monotonicity, exact budget `1/Λ` in YES for every `τ ∈ [0,1]`, and the source
real NO threshold with satisfaction at most `3/4`.

The contract has no Lean inhabitant here. It is finite semantic scope only:
the polynomial-time encoded formula-distribution constructor is missing, as
are the manuscript's AND product, finite empirical list, exact-YES repair,
rational rounding, and encoded source-to-CMMSA reduction. The MZ outer game
and scoped fixed-U decoder still need source-faithful typed domains.

| Lens | Verdict | Evidence and limit |
| --- | --- | --- |
| Lean build | **GO** | `lake build PvNP.RealizableHardness.ActualCoreSourceContractScopesChecks`, 3203 jobs; projection axiom prints contain only `propext`, `Classical.choice`, `Quot.sound`. |
| Proof-adversarial | **GO-WITH-NOTES** | The external assumption is explicit and uniformly quantified over valid finite stars; it is not a proof of HN or an encoded compiler. |
| Complexity theory | **GO-WITH-NOTES** | Global bipartition, `m ≥ 1`, zero-occurrence deletion, universal late `τ`, and real NO threshold match the bounded source scope. Polynomial-time construction remains open. |
| Non-claims boundary | **GO-WITH-NOTES** | This is a scoped typed external contract, not a conditional or unconditional core Theorem 1 certificate. |

Planning review-debt story **S3126** remains open. This bounded contract does
not close the core certificate or reduce the numeric NO-soundness gap.
