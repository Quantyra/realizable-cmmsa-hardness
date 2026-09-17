# Proof-adversarial review: actual tagged-question retained mass

**Verdict: GO-WITH-NOTES.** The frozen increment correctly turns the certified tagged bad-question count into a rational uniform-mass bound, chooses a positive padding count giving bad mass at most `1 / T`, proves the advertised quarter/three-quarter retained-mass consequences for `T >= 4`, and derives positive good cardinality and the reciprocal bounds `<= 4 / 3` and `< 2`. I found no statement mismatch, event mismatch, unjustified division, cast error, inequality reversal, decidability-coherence defect, proof placeholder, or nonstandard axiom. The notes concern the intentionally narrow scope of the reciprocal results and the limited strength of the small-`J` fixtures.

## Frozen scope and evidence integrity

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionRetainedMass.lean` | `22F98B1FF1F84D0BED94744A62873A933C7B531EA310DA953D01B5FBA1581E91` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionRetainedMassChecks.lean` | `9289DD63BEC7798158DF36D7E71D2C0E9365EB34401955C45B6FDF4C7177A2DB` |
| canonical `artifact-hashes.txt` manifest | `3D62FA741B1CC5AE6B8704D52444621059F06063B6812889FF2765D9A2C4E5D1` |

The canonical evidence directory is `research/evidence/2026-09-15-actual-tagged-question-retained-mass-fresh-run/`. I independently recomputed the byte count and SHA-256 digest of every entry recorded in `artifact-hashes.txt`; every entry matches. I also independently recomputed both current source hashes and the manifest hash above. `source-before.sha256` and `source-after.sha256` are identical, and `source-stability.txt` reports `stable=True`.

The receipt records direct `lean.exe` compilation into an isolated target, with main compiled before Checks, both exit codes equal to zero, and neither reviewed object preexisting in the target. The fresh object hashes are `4BF0B86EA74363B9F58CDB97E27D4863402D1913B209E10B30B7CCBF8AFB6AB6` for main and `85B12CFC079580878EEBE701705B4E573A0A89B5D9E09A2FF09457A7EA31864B` for Checks. The two main warnings concern unused `Fintype.card_fun` simp arguments and have no proof effect.

The forbidden-placeholder scan is clean. The exact Checks transcript reports only `propext`, `Classical.choice`, and `Quot.sound` for every reviewed definition and theorem. These are the ordinary Mathlib/Lean classical quotient axioms; there are no user-declared axioms, `sorry`, `admit`, or weakening escape hatches in the frozen sources.

## Exact statements and event normalization

The module defines good and bad subsets of the same finite sample space

```text
Fin J -> Fin K x I.RowId
```

by filtering `Finset.univ` with `GoodOrderedQuestion` and its negation. Both `actualTaggedGoodMass` and `actualTaggedBadMass` divide the corresponding cardinality by exactly

```text
Fintype.card (Fin J -> Fin K x I.RowId).
```

Thus the quantities are uniform masses of ordered, independently tagged row-ID functions. They are not masses over unordered subsets and do not encode a conditional law.

The first quantitative theorem states, under `0 < K` and `0 < m`,

```text
actualTaggedBadMass I K J
  <= (J * (J - 1) * 157) / (K * I.rows.length).
```

Its numerator event is propositionally the exact filter consumed by the imported theorem `tagged_bad_ordered_question_count_mul_rowCard_le`. The proof explicitly bridges the locally elaborated decidability instances using `Finset.ext` and membership simplification. It then rewrites `Fintype.card I.RowId = I.rows.length`; no replacement of the actual row type or predicate occurs.

## Multiplicative count argument and denominator safety

Write `B` for the bad cardinality, `Q` for the total tagged-tuple cardinality, and `R = K * I.rows.length`. The imported certified count gives

```text
B * R <= (J * (J - 1) * 157) * Q.
```

The reviewed theorem proves `R > 0` from `hK` and `I.rows_length_pos hm`. It proves `Q > 0` by the exact finite-cardinality identity

```text
Q = (K * Fintype.card I.RowId) ^ J,
```

where the base is positive because `Fintype.card I.RowId = I.rows.length > 0`. The use of `div_le_div_iff₀` is therefore licensed on both denominators, and `exact_mod_cast` transports the natural-number product inequality to `ℚ` without changing its direction. There is no reliance on Lean's totalized `0 / 0` behavior in any probability-facing theorem.

The separate `actual_tagged_total_question_count_pos` repeats the same valid finite-cardinality argument. It is correctly quantified for every `J`, including `J = 0`, since a function space from `Fin 0` has cardinality one and a positive base to the zeroth power is positive.

## Padding calculation

The imported constructor is

```text
actualPaddingCopies J T = 1 + T * (J * (J - 1) * 157).
```

It is positive for all naturals `J,T`. With `A = J * (J - 1) * 157`, the proof establishes

```text
A * T <= actualPaddingCopies J T * I.rows.length
```

using only `1 <= I.rows.length`, which follows from `0 < m`. This is conservative but correct: `T*A <= (1+T*A)*rows.length` for a nonempty row universe. After proving the two rational denominators positive, cross multiplication yields

```text
A / (actualPaddingCopies J T * I.rows.length) <= 1 / T.
```

The proof requires `0 < T`, exactly as its statement records. The quarter bound then uses `4 <= T` to derive `1/T <= 1/4`; the orientation of this reciprocal inequality and the subsequent transitivity are correct.

## Good/bad partition and retained mass

`actual_tagged_good_bad_card_add_eq_total` identifies the bad filter with the set difference of the universal finite set and the good filter. `Finset.card_sdiff_add_card_eq_card` then gives

```text
good.card + bad.card = total.
```

This proof is coherent despite separately declared classical `DecidablePred` instances: membership is compared propositionally by `Finset.ext`, and both events use the identical `GoodOrderedQuestion` proposition on the identical tagged support. There is no Boolean/propositional mismatch or hidden dependence on a particular proof of decidability.

With positive total cardinality, the rational identity

```text
actualTaggedGoodMass I K J = 1 - actualTaggedBadMass I K J
```

follows from the cardinal partition and valid cancellation of the nonzero total denominator. Combining this identity with bad mass at most `1/4` gives good mass at least `3/4`. This immediately gives strict positive good mass, and hence positive good cardinality. The proof of cardinal positivity correctly rules out the negative-denominator branch of `div_pos_iff` using the separately proved positive total cardinality.

Finally, division by the strictly positive good mass is valid. Cross multiplication from `3/4 <= goodMass` proves

```text
1 / goodMass <= 4 / 3
```

and separately `1 / goodMass < 2`. The strict second result follows because `goodMass >= 3/4 > 1/2`; `nlinarith` is used only after the positive-denominator rewrite.

## Edge cases `J = 0` and `J = 1`

Natural subtraction is intentional. For both `J = 0` and `J = 1`, `J * (J - 1) = 0`, so `actualPaddingCopies J T = 1`. The imported multiplicative count theorem handles `J = 0` separately and forces bad cardinality zero. At `J = 1`, the conflicting-pair characterization has no distinct index pair, so the certified bound again forces bad cardinality zero. The total function space remains nonempty because the tagged row base is nonempty under `hm` and the padding count is positive. Consequently the general proofs yield good mass one, positive good cardinality, and both conditioning-factor inequalities in these cases.

Checks explicitly verifies the padding equalities at `J = 0` and `J = 1`, and applies the quarter bad-mass theorem to a concrete one-row actual instance at both values. These fixtures are useful elaboration checks. They do not state the exact equalities `badMass = 0` or `goodMass = 1`; those facts follow from the generic certified count and partition chain rather than from fixture evaluation. The `J = 2` fixture checks positive good cardinality at the first nontrivial tuple length.

## Assumptions and claim boundary

The assumptions are visible and appropriately placed:

- `0 < m` supplies a nonempty actual row universe through `I.rows_length_pos hm`.
- `0 < K` is required only for a general tagged mass; the padding constructor discharges it automatically.
- `0 < T` licenses the `1/T` bound, and `4 <= T` supplies both positivity and the quarter threshold.
- `N` is unrestricted; no argument requires source variables to be nonempty.
- The constant `157` is inherited from the certified actual conflict-degree theorem.

The finite instance is mathematically coherent: `I.RowId` has the certified cardinality `I.rows.length`, `Fin K x I.RowId` is the tagged row universe, and `Fin J -> ...` is the ordered product sample space. Classical decidability is used only to materialize finite filters.

The exported “conditioning factor” theorems bound the reciprocal of retained good mass. They do not define a conditional distribution, prove normalization or marginals of such a distribution, implement rejection sampling, establish expected or worst-case runtime, transport the ordered law to an unordered subset law, or connect the conditioned law to later star/clique acceptance. Those remain separate downstream obligations and should not be claimed from this increment. Likewise, this increment does not by itself establish an encoded polynomial producer, the manuscript `N_outer` identification, hardness, P versus NP, novelty, or publication readiness.

## Disposition

**GO-WITH-NOTES.** Accept the frozen retained-mass and reciprocal-factor declarations as proof-correct. The notes are claim-boundary and fixture-strength notes, not defects in the theorems: downstream work must still construct and analyze the actual conditional law and its efficient producer, and should add exact small-`J` evaluation only if consumers need those equalities as named interfaces.
