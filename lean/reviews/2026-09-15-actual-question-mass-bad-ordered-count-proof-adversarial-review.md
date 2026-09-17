# Proof-adversarial review: actual question-mass bad ordered count

**Verdict: GO-WITH-NOTES.** The frozen increment proves the advertised generic cardinality bound for bad ordered row tuples. The proof covers all natural-number values of `J`, including `J = 0` and `J = 1`, and remains valid when `E` is empty. I found no weakening, missing hypothesis, arithmetic error, or unsupported conversion between ordered tuples and finite sets. The notes concern fixture coverage and the still-unproved normalization/conditioning consumer; they do not block acceptance of this increment.

## Frozen inputs and certification

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean` | `E87EE1F98ED5D431B288EB88AD278BE05D398461FAE4218A74A0CEDDBC792FC3` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean` | `E4A8CB6663501D7012E967D8B436366536B2AD0D49C6156C0A75882CBE52C36A` |
| canonical `artifact-hashes.txt` | `EB9B26EB3262E97D55B4E4E3BECAF0F01FF5EC46913E9B7152CA2F304C34C8FF` |

The canonical evidence directory is `research/evidence/2026-09-15-actual-question-mass-bad-ordered-count-fresh-run/`. I independently recomputed every hash and byte count listed in its artifact manifest; all entries match. `source-before.txt` and `source-after.txt` record the same two frozen source hashes. The main and Checks exit codes are both `0`, both stderr files are empty, the main object precedes the Checks object, and neither bridge object existed in the isolated target before compilation. The target was seeded from the preceding certified dependency tree while excluding both current bridge objects. The recorded `LEAN_PATH`, Lean `v4.34.0-rc2` toolchain, package revisions, package manifest hashes, seed manifest, commands, and resulting object hashes make the run reproducible at the stated dependency state.

The forbidden scan reports no `sorry`, `admit`, or `native_decide`. The Checks transcript reports only `propext`, `Classical.choice`, and `Quot.sound` for `GoodOrderedQuestion`, the witness equivalence, the generic bad-count theorem, its conflict-degree wrapper, and the preceding bridge theorems. The deprecation and unused-argument linter warnings in the main transcript have no proof-content effect.

## Frozen declaration audit

The four public declarations that constitute the ordered-count increment retain the intended contracts:

1. `GoodOrderedQuestion row u` is exactly injectivity of the ordered tuple together with `ActualStarQuestionSupport.GoodQuestion row (Finset.univ.image u)`.
2. `not_goodOrderedQuestion_iff_conflicting_pair` states both directions of
   `¬ GoodOrderedQuestion row u ↔ ∃ i j, i ≠ j ∧ rowConflict row (u i) (u j)`.
3. `bad_ordered_question_count_le_of_conflict` assumes only the uniform outgoing conflict-neighbourhood bound `C` and concludes
   `#bad ≤ J * (J - 1) * C * |E|^(J - 1)`.
4. `bad_ordered_question_count_le` supplies `C = 1 + 3*D + 9*D^2` by calling the previously certified `conflict_degree_le` with the unchanged three-uniformity and incidence assumptions.

The private helpers `pairConflictSet_card_le` and `distinctOrderedPairs_card` correctly discharge the two counting identities consumed by declaration 3.

## Witness equivalence

Both directions are complete.

- If no distinct pair conflicts, equality `u i = u j` would trigger the reflexive `e = f` branch of `rowConflict`, so `u` is injective. For two distinct values in the image, a failure of row disjointness triggers the direct-overlap branch, and a third row containing one point from each triggers the cross-conflict branch. This establishes both fields of `GoodQuestion`.
- Conversely, a conflicting distinct pair contradicts either tuple injectivity, the pairwise-disjoint field of `GoodQuestion`, or its cross-row exclusion field, according to the three constructors of `rowConflict`.

The use of `Finset.univ.image u` loses tuple multiplicity only after injectivity has been established, so no duplicate-row failure is hidden by image deduplication.

## Fixed-pair count

For fixed distinct positions `i` and `j`, the proof injects a tuple into

`(u i, u j, u restricted to {k // k ≠ i ∧ k ≠ j})`.

The restricted coordinate type has exactly `J - 2` elements. The first value has `|E|` choices, the second has at most `C` choices from its conflict neighbourhood, and the remaining coordinates have `|E|^(J - 2)` choices. The proof therefore obtains

`|E| * (C * |E|^(J - 2)) = C * |E|^(J - 1)`.

The equality is valid because distinct `i,j : Fin J` force `J ≥ 2`; the Lean proof derives the required truncated-subtraction identity with `omega`. It also remains valid for `E = ∅`: when `J ≥ 2` there are no tuples, and both sides of the final power identity are zero. The proof needs only an injection and a containing target, so overlap among intermediate `biUnion` fibers can only make its upper bound more conservative.

## Ordered-pair factor and global union

`distinctOrderedPairs_card` partitions ordered pairs by their first coordinate. Each fiber contains exactly `J - 1` second coordinates, and distinct first-coordinate fibers are disjoint. Hence its cardinality is exactly `J * (J - 1)`, rather than an unordered-pair count or a looser `J^2` count.

The bad set is included in the union of the fixed-pair conflict sets by the witness equivalence. Applying the finite union bound and the fixed-pair estimate gives exactly

`J * (J - 1) * C * |E|^(J - 1)`.

Possible multiple witnesses for one bad tuple cause only overcounting and do not invalidate the upper bound.

## Boundary branches

The generic proof separates `J < 2` before constructing distinct positions.

- For `J = 0`, the unique empty tuple is injective and its empty image satisfies both universal fields of `GoodQuestion`, so the bad set is empty.
- For `J = 1`, every existing tuple is injective and its singleton image is good; if `E` is empty there are no such tuples. The bad set is again empty.
- For `J ≥ 2` and `E = ∅`, the function space `Fin J → E` is empty, so the bad set and every fixed-pair conflict set are empty. The cardinal arithmetic used in the proof evaluates consistently, including the `J = 2` exponent-zero intermediate term.

The Checks module explicitly compiles the `J = 0` and `J = 1` applications. It does not contain a separate empty-`E` fixture, but the theorem proof handles that branch without a positivity assumption or division, so this is fixture debt rather than a theorem gap.

## Fixtures and limitations

The `mixedRows` fixture is useful and nonvacuous: it exercises reflexive conflict, direct overlap, a disjoint cross-only conflict, and the full `bad_ordered_question_count_le` wrapper on `J = 2`. Together with the two small-`J` fixtures, it covers every logical branch that materially drives the theorem. The Checks file does not separately instantiate the iff in both directions, the fixed-pair helper, or an empty row type. Those additions could improve regression localization, but the exact theorem signatures and kernel-checked proofs already appear in the certification transcript; duplicating them is not required for acceptance.

This result is a cardinality statement for the uniform finite ordered-tuple space. It does not yet prove a probability bound, positivity of the total mass, a conditioning estimate, preservation of marginals after conditioning, the actual-source specialization, actual-star acceptance, or any headline hardness theorem.

## Direct next consumer

Accept the frozen bad-ordered-count increment. Its direct next consumer should divide the count by `|E|^J` under the necessary nonemptiness/positivity and size hypotheses to prove the retained `GoodOrderedQuestion` mass bound. The subsequent conditioning lemma must then quantify the loss and any required marginal distortion. The actual incidence theorem can specialize `D = 4`, giving conflict constant `157`, when this generic probability statement is instantiated on the constructed occurrence-row source.
