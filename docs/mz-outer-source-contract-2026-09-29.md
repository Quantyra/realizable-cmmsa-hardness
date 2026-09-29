# Bounded MZ outer source contract

**Status:** `ActualMZOuterSourceContract.lean` declares an uninhabited
`ExternalMZOuterSource` structure. It is an external premise, not a proof of
MZ or a theorem about the manuscript's CMMSA verifier. The targeted Lean
module built green (3416 jobs). `ActualMZOuterSourceContractChecks.lean`
built green (3417 jobs); its projection axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. That audit does not provide an
inhabitant of the contract.

## Source and quantifiers

[MZ, Theorem 3.1](https://arxiv.org/pdf/2510.23991v1) supplies an absolute
soundness fraction `s<1` and, for every fixed positive outer YES error
`ε₁` with `ε₁<1-s`, a polynomial-time SAT-to-Gap3Lin reduction. Its output
has three distinct variables per equation, at most ten equations per
variable, and at most one shared variable between two different equations.
The Lean interface fixes a bit encoding first, and requires an actual
zero-coin `SeededMap` whose `run` is in `FP`; its output parses to such an
instance. It preserves near satisfiability and the absolute NO gap. The
encoding parser and its computational properties remain part of the external
interface, not a constructed result in this file.

[MZ, Section 3.2 and Claim 3.2](https://arxiv.org/pdf/2510.23991v1)
define independent sampling of `J` rows, all-three retention with probability
`1-β` or a uniform singleton with probability `β`, and `r` independent
uniform advice vectors on retained coordinates. The contract's exact
point mass is the product of these row masses. For near error `ε`, it posits
strategies winning with probability at least `1-Jε`. For an absolute
`κ>0`, fixed before the later `ε₁`, every pair of strategies on a NO
instance wins with probability at most
`2^(-κ(1-s)^2 2^(-r) β J)`. The source's asymptotic `Ω` is represented
by that fixed external `κ`, not derived in Lean.

The first prover receives row identities and zero-extended advice. Its
accepted answers are consistent whenever two sampled rows share a variable,
and satisfy every equation. The second receives indexed retained variables
and advice without row identities; accepted answers agree on retained
coordinates. This is the indexed product-game interpretation of the source.

## Boundary and exact remaining dependencies

The paper uses both a union of retained variable sets and concatenated
independently sampled row advice. Repeated sampled rows can overlap, so
those descriptions do not automatically define the same second question.
The [source-question audit](mz-outer-source-question-mismatch-2026-09-29.md)
identifies the first missing theorem: a success-preserving map from the
manuscript decoder's actual observation and conditioned legitimate event to
strategies for this exact indexed product game, with the required
conditioning factor. The fixed encoding, bounded-occurrence SAT reduction,
exact product law, and source value bounds are all still **external fields**
of `ExternalMZOuterSource`; no inhabitant is constructed here. Its interface
does not include changed-ambient 8S, representative selection, the
manuscript's YES verifier law, or the final NO contradiction.

The new declarations improve the precision of the conditional certificate
but do **not** reduce the remaining NO-soundness gap by themselves.
