# Tagged question-mass bridge: non-claims-boundary review

2026-09-15. Read-only review of the frozen `TaggedQuestionMassBridge` increment, its Checks module, and the routed fresh-run evidence. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment proves an unconditioned product equivalence for ordered tagged tuples and an exact base-event fibre count, an exact characterization of conflict in a tagged copy, and union-bound upper bounds on the number and uniform mass of bad ordered questions. The Checks module supplies small finite fixtures for the product/base-event count and one tagged bad-event instance.

This verdict authorizes only the tuple-equivalence, unconditioned base-pushforward counting, tagged-conflict equivalence, and bad-count/bad-mass upper-bound wording below. It does not authorize general exact bad-event scaling, uniformity after conditioning on good questions, clique or stationarity claims, a producer, star acceptance, hardness, P-versus-NP, novelty, or publication claims.

## Frozen artifacts and certification evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedQuestionMassBridge.lean` | `B258BB7FE60CFC4D7AA17F45427B94060B3F896D9A5565DE2EA07B2D7C349CBE` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedQuestionMassBridgeChecks.lean` | `35CFE1C0AE7B8C9C9309973D86E21BCC514BFDBFDFA01AD43CE2593B0CA655A6` | Matches the routed freeze. |
| `research/evidence/2026-09-15-tagged-question-mass-bridge-fresh-run/bundle-manifest.txt` | `735382C87BD28B428F3076B7718DC7432E62CBCF63A41C0FD43C03AC0540E89F` | Matches the routed evidence-manifest hash. |

The bundle records unchanged before/after source hashes, final main and Checks exit codes `0`, empty final stderr, and emitted object hashes `93670709D4269EAD91230A4CB7A89351E75D89DECBC6D5061E254B2F19027EA2` and `FE510A8CA3F46FA4D76EA9D695081EE743B957EC3FE6D8DC9571352E862B3649`. The target directory was seeded with 2,800 dependency objects while excluding the two reviewed target objects; the final inventory contains both newly emitted target objects. This certifies direct compilation of the frozen main and Checks files against the recorded seeded dependencies. It is not evidence of an independent clean rebuild of every transitive dependency.

The recorded forbidden-token scan is empty, and an independent read-only scan found no `sorry`, `admit`, `native_decide`, or source-level `axiom` in the two frozen files. The Checks transcript reports no axioms for `tagProjection` and `baseProjection`; the equivalence declarations use the listed standard Lean foundations, and the remaining reviewed theorems report only `[propext, Classical.choice, Quot.sound]`. No project-specific axiom is reported.

The bundle preserves an earlier Checks-only fixture failure and its repair. That failure concerned reconstruction of concrete `Fin 2 × Unit` values and proof that the two constant tuples differ; it did not reject or change a main theorem statement. The final Checks run succeeds.

## Exact theorem boundary

For ordered tuples `u : Fin J → Fin K × Row`, `taggedTupleEquiv` gives an exact equivalence

`(Fin J → Fin K × Row) ≃ (Fin J → Fin K) × (Fin J → Row)`

by separating each tuple into its tag projection and base-row projection. The associated cardinality theorem is exact. For every finite base event `A`, `baseProjection_event_card` proves that its full, unconditioned preimage has cardinality

`K^J * A.card`.

Thus the module supports an exact counting description of the unconditioned base projection. When the relevant finite uniform laws are defined on nonempty spaces, this count identity supports saying that forgetting independent full-space tags pushes the unconditioned uniform tagged-tuple law to the uniform base-tuple law. The theorem does not restrict to good tuples and says nothing about the base marginal after conditioning or rejection.

For a semantic finite 3-LIN source `I`, `taggedCopy_rowConflict_iff` proves the exact pairwise statement

`rowConflict (I.taggedCopy K).support e f ↔ e.1 = f.1 ∧ rowConflict I.support e.2 f.2`.

Consequently, `taggedCopy_not_good_iff` says that a tagged ordered tuple is bad exactly when two distinct positions share a tag and their base rows conflict. `taggedConflictFibreEquiv` further identifies the conflicting tagged rows at a fixed tag with the conflicting base rows.

Given the hypothesis that every base row conflicts with at most `C` base rows, the quantitative conclusions are upper bounds:

- `tagged_bad_ordered_question_count_le` bounds the bad-tuple count by `J * (J - 1) * C * (K * card Row)^(J - 1)`;
- `tagged_bad_ordered_question_count_mul_rowCard_le` gives the corresponding cross-multiplied count bound;
- under `0 < K` and `0 < card Row`, `tagged_bad_ordered_question_uniform_mass_le` bounds the full-space uniform bad fraction by `J * (J - 1) * C / (K * card Row)`.

These results use a union-bound style count over ordered position pairs. They do not state equality for the full bad event, disjointness of pairwise bad witnesses, tightness, or an exact asymptotic law. The rational upper bound may exceed one and, by itself, does not prove useful retained good mass.

## Fixture audit

The Checks module proves that a singleton base event in the example with `J = 2`, `K = 2`, and three base rows has tagged preimage cardinality `4`, while the full tagged tuple space has cardinality `36`. This concretely exercises the exact product/base-event counting identity.

For the one-row source with `J = 2` and `K = 2`, the Checks module proves that exactly two of the four ordered tagged tuples are bad: the two constant-tag tuples. It also successfully instantiates the rational upper-bound theorem with `C = 1`; in this example the displayed upper bound is `1`, while the exact bad fraction is `1/2`. This is evidence that the general mass theorem is an upper bound rather than an exact scaling theorem.

The evidence explicitly records that an optional nonuniform conditioned fixture is absent. The fixtures therefore do not test conditioning on good tuples, a conditioned base marginal, clique resampling, stationarity, a producer, or a star consumer.

## Permitted wording

The strongest justified description is:

> Lean separates every full-space ordered tagged tuple into its tag tuple and base-row tuple, proves the exact cardinality of every unconditioned base-event fibre, and characterizes tagged row conflict as same-tag base conflict. If every base row has at most `C` conflicts, it proves union-bound upper bounds on the number and full-space uniform mass of bad ordered tagged tuples, including bad mass at most `J(J-1)C / (K|Row|)` when `K` and `|Row|` are positive.

Acceptable shorter descriptions are “unconditioned tagged/base tuple factorization,” “exact unconditioned base-event fibre count,” “same-tag conflict iff base conflict,” and “union-bound bad ordered-question count and uniform-mass upper bound.” If “pushforward” is used, it must refer to the unconditioned full finite uniform law and retain the required nonemptiness for probabilistic wording.

Do not describe this increment as proving or certifying:

- exact general scaling or equality for the full bad-event count or probability;
- uniformity, independence, or a base-law identity after conditioning on good questions;
- positive retained mass or a useful below-one bad-mass bound without additional numerical hypotheses;
- clique resampling, stationarity, mixing, or another Markov-chain property;
- an encoded, computable, polynomial-time, or output-size-bounded producer;
- star acceptance, a completed source-law instantiation, a randomized reduction, or a hardness consequence;
- P versus NP, circuit or proof-system lower bounds, or another complexity separation;
- novelty, manuscript correctness, publication readiness, or route-final completion.

## Material notes

1. The exact results concern the full unconditioned tuple space, base-event fibres, and local conflict equivalences.
2. The bad-count and bad-mass theorems are one-sided upper bounds; the exact `2`-bad-tuples statement belongs only to the small one-row fixture.
3. The normalized mass theorem requires `0 < K` and a nonempty base row type. It does not assert that its right-hand side is below one.
4. Conditioning can bias the base projection because goodness depends jointly on tags and base conflicts; no conditioned-uniformity theorem or fixture is present.
5. The certification evidence is adequate for the frozen two-file increment, with its seeded-dependency scope stated above.
6. No public-claim promotion follows from this review.
