# Actual `D = 4` bad-question count: complexity-theory and manuscript review

Date: 2026-09-15  
Lens: top-level complexity theory / manuscript alignment  
Verdict: **GO-WITH-NOTES**

## Review scope and frozen artifacts

This review was read-only with respect to the frozen Lean sources. I inspected the two target modules, their canonical certification evidence, the actual allocation and degree producers, the submission manuscript, the current obligation ledger, and the preceding generic-count review. I made no Lean edit, ran no compilation, and performed no commit, push, release, or public action. This file is the only artifact written by this review.

- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean`: SHA256 `57159656B9F2721BE7ACD180B5F7C3208D4EA9313AA90204DB99ADD662018BCA`.
- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean`: SHA256 `7A54A9CABA5C1553E018F37D29C41A3FB81741FED251E7CCA0ADAE9E9EF3E622`.
- Canonical evidence: `research/evidence/2026-09-15-actual-question-mass-d4-count-fresh-run/`.
- Evidence manifest `artifact-hashes.txt`: SHA256 `EF3DA1028341BA32E38D172D5F7D35C62338F20323CC9B16F9D4E283DC59421B`.
- Manuscript `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`: SHA256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`.
- Planning ledger `C:/Users/Dan/Desktop/Projects/IGH/Quantyra-Planning/docs/research/pvnp/full-theorem-obligation-ledger.md`: SHA256 `E31FD28BA44ADA94840926140CCDD349872C6361E8C1CE610DEEBB3B6EEA814A` at review time.

The evidence records main and Checks exits `0`, empty stderr, matching before/after source hashes, and fresh target objects with hashes `BC655AD95C0BB5D283C54865E4F30B314B3CB3861E6E55BAD50DBC2F0318A153` and `0F2FA5AF2886FA6B9CD6A594FFF0D827086FB03BE6678A90A1D0DB059624A902`. The forbidden-token scan found no `sorry`, `admit`, or `native_decide`. All eight printed declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The target objects were absent before compilation; 2,794 dependency objects were seeded from the preceding canonical run. This is a fresh target build with disclosed pinned dependencies, rather than a rebuild of every dependency from source.

## Exact specialization

The new construction-specific theorem is

```lean
theorem actual_bad_ordered_question_count_le
    {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) :
    ((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card ≤
      J * (J - 1) * 157 * (Fintype.card I.RowId) ^ (J - 1)
```

It introduces no premise beyond the actual occurrence allocation `I` and tuple length `J`. It instantiates the already reviewed generic theorem with

```text
E   = I.RowId
X   = I.GlobalVar
row = I.support
D   = 4.
```

Both substantive inputs are supplied by the actual construction on exactly this occurrence-indexed universe:

1. `I.support_card` proves `(I.support q).card = 3` for every original or equality-cloud row. Thus the three-uniformity premise is discharged, including distinctness of the three support coordinates.
2. `rowId_incidence_card_le_four I x` proves that at most four `RowId`s contain each global variable. Its preceding identity theorem equates this row-ID filter cardinality with `ActualOccurrenceDegree.degree I x`. The degree producer proves port degree at most `1 + 3 = 4` and internal degree exactly `2`. Therefore the specialization does not assume degree four, deduplicate equal owners, or change from row occurrences to row values.

The theorem uses `I.support_card` and `rowId_incidence_card_le_four` directly. Repeated source owners remain separated through occurrence anchors and distinct row identities, which is the representation needed for uniform sampling of equation occurrences.

## Meaning of `157`

The number is the normalized value of the generic conservative conflict-neighbourhood bound:

```text
1 + 3D + 9D² = 1 + 3·4 + 9·4² = 157.
```

For a fixed row `e`, the three summands cover:

- the identical row;
- rows directly sharing a coordinate with `e`, bounded by `3D`; and
- rows with a cross witness through another row, bounded by `3 · D · 3 · D = 9D²`.

Overlaps between these candidate families only make the actual neighbourhood smaller. Hence `157` is an upper bound on the number of row identities conflicting with one fixed actual row. It is not asserted to be tight, the exact conflict degree, the number of bad questions, or a probability by itself.

Combining that neighbourhood bound with the `J(J-1)` ordered choices of two distinct positions gives the displayed bad-tuple count. The remaining `J-1` row values are unrestricted, producing the factor `|I.RowId|^(J-1)`. The already reviewed small-`J` branch makes the bad set empty for `J = 0` and `J = 1`, so the specialization is valid for every natural `J`.

## Relevance to the manuscript's uniform question law

The finite type `Fin J → I.RowId` is exactly the sample space for `J` independent uniform row draws with replacement. Its cardinality is `M^J`, where `M = Fintype.card I.RowId`. `GoodOrderedQuestion I.support u` requires injectivity and applies the manuscript's two geometric legitimacy conditions to `Finset.univ.image u`: selected rows have disjoint supports, and no ambient row contains one coordinate from each of two selected rows. This matches manuscript lines 162--180 and supplies the raw counting input for the discarded-illegitimate-tuple argument at lines 1148--1158.

When `M > 0`, division by the total sample-space size gives

```text
Pr[bad] ≤ 157 * J(J-1) / M.
```

That normalized statement is an immediate mathematical consequence, but it is not a declaration in the frozen module. The count alone also does not show that the right side is below one or below the manuscript's chosen `a`; usefulness requires a sufficiently large positive row count.

## Remaining probability and distribution obligations

| Obligation | What this increment supplies | What remains |
|---|---|---|
| Probability normalization | Numerator bound on the uniform ordered function space | Define the exact rational or real uniform law, prove `card (Fin J → I.RowId) = M^J`, establish `M > 0`, and derive the ratio bound without a zero denominator |
| Row nonemptiness | `I.RowId` contains the original `Fin m` summand, and `I.rows.length = M` is derivable from the existing enumeration | Export the bridge from the manuscript/source premise `0 < m` to `0 < M`; the theorem currently also permits empty instances, for which a positive-row sampling law is unavailable |
| Disjoint-copy padding | The bound improves as `M` grows while the local constant stays `157` | Define copied row, variable, support, and RHS universes; prove cross-copy disjointness, degree at most four, row count multiplication, polynomial size, and preservation of YES/NO violation fractions and source value |
| Retained mass | `Pr[bad]` has the required `O(J²/M)` form once normalized | Choose the copy count so `157J(J-1)/M ≤ a ≤ min(tau/100, 1/4)`, then prove `Pr[GoodOrderedQuestion] ≥ 1-a > 0` |
| Conditioning | Identifies the event on which to condition | Construct or characterize the conditional law and prove the manuscript's failure inflation `Pr[failure | good] ≤ Pr[failure]/(1-a)`; an efficient rejection sampler or equivalent enumerated sampler remains separate |
| Ordered-to-subset bridge | Each good ordered tuple yields the legitimate support set `Finset.univ.image u` | Prove this set has cardinality `J`, prove equal fibre size (each legitimate `J`-set has `J!` orderings), and establish the required pushforward/uniformity statement for the later span-based question object |
| Weighted law | The initial row product law is uniform, as required by the current manuscript setup | Show that later choices and clique resampling leave the `U` marginal uniform, using equal dimensions/fibre counts as claimed at manuscript lines 1155--1158; arbitrary nonuniform or weighted row laws would need a separate weighted-conflict estimate or maximum-atom bound |

The copying obligation needs particular care about which representation is copied. Copying the final semantic row/RHS system with disjoint variable tags plainly preserves its uniform violation fraction, while copying the raw source and rerunning occurrence regularization requires a commutation or value-transfer theorem. Either route must connect the copied row count used in the probability denominator to the manuscript's `N_outer` notation and to the actual encoded producer.

The weighted star-projection CSP and its occurrence weights are downstream objects. This theorem controls the initial uniform equation-tuple marginal only. It does not justify transferring the `157J(J-1)/M` estimate to an arbitrary star-edge distribution. The manuscript's claimed uniform clique-resampled marginal is therefore still a real theorem obligation, not a consequence of this count.

## Headline dependency boundary

This increment completes the construction-specific finite-count edge:

```text
actual three-uniform supports + actual incidence D=4
  → actual conflict degree at most 157
  → actual bad ordered-question count.
```

The next direct work is probability normalization and row nonemptiness, followed by disjoint-copy padding, retained-mass positivity, conditioning, and the ordered-to-subset law. The larger path still requires the RHS functional and `dim H_U = J`, overlap agreement and minimal label transport, an actual star and acceptance theorem, the clique-resampling marginal, rational edge/formula tables, a concrete polynomial-time seeded reduction and probability bridge, headline randomized-reduction assembly, the learning corollary, and manuscript reconciliation.

No theorem in this increment establishes the actual-star distribution, a source hardness theorem, an NP-hardness reduction, P versus NP, the full manuscript theorem, novelty, or publication readiness.

## Decision

**GO-WITH-NOTES.** The frozen theorem correctly discharges the planned actual-source specialization. The actual occurrence allocation supplies three-element supports and incidence at most four without additional assumptions, and the arithmetic constant `157` is the correct conservative conflict-neighbourhood value. The resulting count is exactly relevant to independent uniform ordered row draws.

The notes are substantive remaining dependency edges rather than defects in this theorem: positive row count, normalized probability, copy construction and value preservation, a useful retained-mass bound, conditioning, ordered-to-subset pushforward, the later uniform-marginal/weighted-law bridge, and every subsequent actual-star and headline assembly step remain open.
