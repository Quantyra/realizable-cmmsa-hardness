# Proof-adversarial review: finite 3-LIN optimum and tagged-copy value

**Verdict: GO-WITH-NOTES.** The frozen increment defines an attained finite minimum violation count, proves exact multiplication of that minimum under independently tagged copies for every `K : Nat`, and derives preservation of the real-valued minimum violation rate and satisfaction value when `0 < K` and the base row type is nonempty. The two directions of the optimum theorem are correctly distinct: one repeats a base optimizer, while the other restricts an arbitrary copied optimizer tag by tag. The `K = 0` case of the natural-number minimum theorem is valid and does not require a nonexistent tag. No HIGH or MEDIUM proof-adversarial issue was found.

The notes are boundary conditions. `minimumViolationRate` is a total real-valued definition, so an empty row universe uses Lean's `0 / 0 = 0` convention and `value = 1`; probability-facing consumers must retain the explicit nonempty-row hypothesis. The positive-copy hypothesis is necessary for general rate preservation. This increment does not supply the encoded copy producer, the global independently tagged `J`-row law, a chosen polynomially bounded `K`, positive retained mass, conditioning, or any headline consequence.

## Frozen artifacts and certification

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/Finite3LinOptimum.lean` | `A4FD9733CB93D08E04D1091F07F27C359CA1F16A12E487FC3D40F43F1558E6D2` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/Finite3LinOptimumChecks.lean` | `EBDDBBC5EB1277A54E60CDF843AE0FFB4FF1FEC307A83625F99EF1EB46C25A9F` |
| canonical `bundle-manifest.txt` | `536F9F5CCE3B6CB1DA79B9C1FCA84B735E3F377DC10DA2B0719E8BF050C91485` |

The evidence directory is `research/evidence/2026-09-15-finite-3lin-optimum-fresh-run/`. I independently recomputed all three frozen hashes and verified every entry in `bundle-manifest.txt`. Preflight records a newly created target with both reviewed objects absent before compilation and stable before/after source hashes. The main and final Checks runs exited `0` with empty stderr. Their emitted object hashes are `596EFBD09A22810D69BCAE0A90EBCF589131A98854336F666131860BDC23C71D` and `492091452AFA9FFF65D12B215F5440B206F5B0F8B28CB6A543361E36E6DDF538`.

The three recorded failed Checks attempts are certification setup failures, not failed theorem attempts. Attempts one and two could not find the new `Finite3LinOptimum.olean`; attempt three found that object but could not find the seeded `TaggedFinite3LinSource.olean`. After the dependency objects were placed under the first effective `LEAN_PATH` root, the same frozen Checks source compiled successfully. The failures are preserved transparently and do not contradict the final successful certification.

## Finite minimum and attainment

For `I : Finite3LinSource Row Var`, the assignment space `Var -> ZMod 2` is finite because both `Var` and `ZMod 2` are finite. It is also nonempty even when `Var` is empty: there is a unique function from the empty type. Thus

```text
Finset.univ.image I.violations
```

is a nonempty finite set of natural numbers. `minViolations` uses `Finset.min'` with a proof obtained from `Finset.univ_nonempty`, so the definition does not smuggle in a source satisfiability, positive-row, or positive-variable assumption.

`minViolations_le_violations` places an arbitrary assignment in that image and applies the defining minimum property. `exists_violations_eq_minViolations` uses `Finset.min'_mem` and extracts the assignment from image membership. Consequently the minimum is both a lower bound for every assignment and actually attained. This is stronger and more useful than merely taking an infimum over natural numbers.

## Exact tagged-copy minimum

The theorem

```text
(I.taggedCopy K).minViolations = K * I.minViolations
```

has both required inequalities.

For `copied minimum <= K * base minimum`, the proof selects an attaining base assignment `x`, repeats it independently on every tag, applies copied minimality to that explicit candidate, and rewrites its violation count using `taggedCopy_repeatAssignment_violations`. This direction establishes an upper witness for the copied optimum and uses no claim that all copied optimizers must repeat the same assignment.

For `K * base minimum <= copied minimum`, the proof selects an attaining copied assignment `y`. This witness is otherwise arbitrary and may use a different base assignment on every tag. `taggedCopy_violations` decomposes its violation count as

```text
sum k : Fin K, I.violations (restrictAssignment y k).
```

Every summand is at least `I.minViolations`; summing those inequalities gives the lower bound. This is the separability argument needed to rule out a copied optimizer improving on `K` independent base optima. It does not assume consistency between tags or a false uniqueness property.

At `K = 0`, the repeated assignment is a function on an empty variable carrier, the copied optimizer exists because that function space is still inhabited, and the lower-bound sum has no indices. Both sides reduce to zero. The proof never constructs `k : Fin 0`, and the dedicated fixture confirms `(contradictoryTwoRow.taggedCopy 0).minViolations = 0`.

## Real rate, value, and cancellation assumptions

The definitions are exactly

```text
minimumViolationRate I = (I.minViolations : Real) / (Fintype.card Row : Real)
value I                = 1 - I.minimumViolationRate.
```

After rewriting the copied minimum and `card (Fin K x Row) = K * card Row`, rate preservation is cancellation of the same real factor `K` from numerator and denominator. The hypotheses `0 < K` and `0 < Fintype.card Row` imply both factors are nonzero, so `field_simp` is justified. There is no natural-number truncation because the numerator and denominator are cast to `Real` before division.

The `0 < K` condition is materially necessary: a zero-copy instance has zero rows and minimum violation rate `0`, which need not equal the base rate. The nonempty-row condition is the correct probability-semantic guard and is sufficient for cancellation. With Lean's total division it is stronger than needed for the narrow equality when the base row type is empty, because both base and copied rates then evaluate to zero; retaining it avoids presenting `0 / 0` as a normalized probability. `taggedCopy_value` is a direct congruence consequence of rate preservation and introduces no additional arithmetic assumption.

This module defines the objectives but does not prove the general bounds `0 <= minimumViolationRate <= 1` or `0 <= value <= 1`. Those bounds follow only after relating minimum violations to row count and are not required for the exact preservation statements reviewed here. Downstream code should not cite their existence from this increment.

## Fixture audit

`contradictoryTwoRow` contains two copies of the same three-variable left-hand side with opposite right-hand sides. Every assignment violates exactly one of them, and the Checks proof establishes `minViolations = 1` using both an explicit upper witness and positivity for an arbitrary attaining assignment. This is a nonzero, unsatisfiable fixture rather than a vacuous satisfiable case.

The fixtures then check zero-copy minimum `0`, three-copy minimum `3`, base rate and value `1/2`, and preservation of both quantities under three copies. They exercise the multiplication and real normalization at a nontrivial numerator and denominator. They do not include a zero-copy rate equality, appropriately, because the generic rate theorem excludes that false case. The generic lower-bound proof, rather than a fixture, provides coverage for an optimizer whose restrictions differ between tags; the preceding `TaggedFinite3LinSource` Checks module separately exercises a mixed copied assignment.

## Axioms and forbidden scan

The source scan is clean for `sorry`, `admit`, `native_decide`, and user-declared axioms. The only occurrences of the word `axioms` in the Checks source are the intended `#print axioms` audit commands. The recorded forbidden-scan exit is `1` with an empty matches file, the normal no-match result for the scan.

The axiom transcript reports only `propext`, `Classical.choice`, and `Quot.sound` for all eight reviewed declarations. These are standard Lean/Mathlib logical dependencies of finite-set minima, function extensionality, and quotient-backed structures. There is no theorem-specific axiom, `sorryAx`, or native evaluation dependency.

## Direct consumer and disposition

The immediate direct consumer is the actual-source specialization for source-preserving tagged-copy padding (S3138): instantiate the generic results at `Finite3LinSource.ofActual I`, rewrite assignmentwise semantics with `Finite3LinSource.ofActual_violations`, and rewrite the base row denominator with `rowId_card_eq_rows_length`. This supplies exact preservation of the actual semantic source's optimum violation fraction and satisfaction value for positive `K` and nonempty source rows.

That specialization should then feed the explicit polynomially bounded choice of `K` and the retained-mass calculation. S3138 still separately requires the encoded copy producer and size/runtime proof, structural copied-source invariants, the global uniform independently tagged `J`-row law and projection, the manuscript `N_outer` identification, and strict positive retained mass before conditioning. The present theorem is a sound direct input to those obligations; it does not discharge them or justify closing S3138.

**Final proof-adversarial disposition: GO-WITH-NOTES.** Accept the frozen minimum, attainment, exact tagged-copy minimum, rate, and value declarations for their stated semantic use. Preserve the positivity hypotheses at every normalized consumer and keep all broader route and claim gates open.
