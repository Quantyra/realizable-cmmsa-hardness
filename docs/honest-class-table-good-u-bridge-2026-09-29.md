# Honest class table for the copied verifier

`ActualHonestTaggedTransport.lean` constructs a single legal predraw leaf
table from **any** ambient linear assignment `f`, including one that violates
some copied equations. For each quotient class it chooses a presentation on
which `f` satisfies the rows if one exists, and otherwise uses a valid fallback
RHS label. It transports that seed to each full vertex in the class. The center
table is the restriction of the same `f`.

The Lean theorem `honestOriginalAccepts_of_goodU` quantifies over every source
instance, copy count, verifier dimensions and arity, ambient functional `f`,
and actual `OriginalDraw x`. Its only equation premise is that `f` satisfies
every row in **that draw's** `x.U.rows`. It concludes
`originalAccepts I copies (honestOriginalAssignment I copies f) x`. The sampled
representatives need not satisfy `f`'s equations. The key proof is tagged
transport coherence through a possibly bad representative, followed by the
good class seed's honest restriction on the queried full leaf.

For the manuscript's `m+1` blocks, instantiate this same fixed table at the
original block and at every clique-resampled block. The all-good-row event
then implies acceptance of every block pointwise. This requires a Lean joint
experiment carrying all those blocks with the manuscript's shared state and
legitimacy conditioning. The present `OriginalDraw`/`originalLaw` represents
one copied source block; it does not itself provide that joint experiment or
the conditioned marginal bound for each resampled `U`. Those probability
statements must be established before `ActualLateTauYesComposition` yields
the YES probability. The source outer assignment must also be transported to
the tagged ambient functional and its copied bad-row law checked.

This result does not change the NO-soundness gap. It removes the prior
representative-good premise from the pointwise YES acceptance step.

## Verification and bounded review

`lake build PvNP.RealizableHardness.ActualHonestTaggedTransportChecks` passed
(3262 jobs). `#print axioms` for tagged transport coherence, class-table
legality, good-target transport, and actual good-`U` acceptance reports only
`propext`, `Classical.choice`, and `Quot.sound`.

| Lens | Bounded pointwise result | Core certificate |
| --- | --- | --- |
| Proof adversarial | GO-WITH-NOTES | NO-GO |
| Complexity theory | GO-WITH-NOTES | NO-GO |
| Non-claims boundary | GO-WITH-NOTES | NO-GO |

The review is bounded to the copied verifier's pointwise class-table result.
No joint `m+1` law, marginal error estimate, encoded SAT reduction, or NO
decoder follows from it.
