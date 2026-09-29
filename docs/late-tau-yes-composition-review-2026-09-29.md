# Late-τ YES composition: bounded review

Scope: manuscript `paper/body.tex` equation (21) and the surrounding YES
paragraphs. The Lean module is
`ActualLateTauYesComposition.lean`; its separate Checks target built green
(3234 jobs), with only `propext`, `Classical.choice`, and `Quot.sound` in the
reported axiom set.

For any finite law `μ`, any `m`, positive `J`, positive rational `τ`, rational
`ε₁ ≤ τ/[100(m+1)J]`, legitimate event of mass `1-a` with `a ≤ 1/4`, and
`m+1` block-failure events satisfying the **joint numerator** bound
`μ(legitimate ∩ badᵢ) ≤ J ε₁` for every `i`, Lean proves

`μ(legitimate ∩ ⋃ᵢ badᵢ)/μ(legitimate) ≤ τ/75 < τ`.

The companion theorem names the complementary probability of *good blocks*;
it does not identify those blocks with the actual PCP accepts event.
Dependence among resampled blocks is unrestricted in this union bound.

| Lens | Bounded finding | Core finding |
| --- | --- | --- |
| Proof-adversarial | GO-WITH-NOTES for the finite-law union and conditioning calculation, after changing to the legitimate-event numerator. | INCOMPLETE: actual block law and accepts-event containment are absent. |
| Complexity theory | GO-WITH-NOTES for the numerical late-`τ` calculation with fixed `m,J`; no claim about runtime follows from this finite-law theorem. | INCOMPLETE: encoded padding and source reduction are absent. |
| Non-claims boundary | GO-WITH-NOTES after naming the result good-block probability and displaying every law premise. | INCOMPLETE: no PCP or Theorem 1 certification follows. |

Exact outstanding interfaces, in manuscript quantifier order:

1. Fix the NO-side `κ`, then `A`, then `m,h,J,β` independently of the later
   positive target `τ`. For each `τ>0`, use the **external** positive-error
   SAT-to-bounded-occurrence-3Lin result to choose some `ε₁>0` no larger than
   `τ/[100(m+1)J]`; the source NO gap must remain absolute and independent of
   `ε₁`. Lean has the positive numerical candidate, not this encoded source map.
2. Construct enough disjoint copies and prove the actual ordered source law
   has illegitimate tuple mass `a ≤ min(τ/100,1/4)`, preserving the bounded
   occurrence promise and polynomial runtime for fixed parameters.
3. On that law prove `μ(legitimate ∩ badᵢ) ≤ J ε₁` for the original block and
   **every** clique-resampled block. In particular, prove the resampled
   eligible-question marginal and its row-equation satisfaction transport.
   The current tagged law proves only the initial eligible-`U` marginal.
4. Define the actual honest PCP accepts event and prove that on legitimate
   tuples, all `m+1` equation blocks satisfied imply acceptance. Only then
   can this good-block probability yield the manuscript YES guarantee.

This increment does not reduce the numeric NO-soundness gap. Theorem 1 remains
conditional, and the three-lens table is not a route-final closeout.
