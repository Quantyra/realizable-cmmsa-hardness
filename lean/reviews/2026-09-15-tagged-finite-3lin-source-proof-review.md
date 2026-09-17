# Proof-adversarial review: tagged finite 3-LIN semantic copies

**Verdict: GO-WITH-NOTES.** The frozen increment correctly constructs disjointly tagged semantic copies of a `Finite3LinSource`, proves exact row-local and assignmentwise correspondence, decomposes the copied violation count into the sum of the per-tag violation counts for every assignment, and proves multiplication by `K` for a repeated base assignment. The statements include the `K = 0` case and handle it correctly. No hidden positivity premise, cancellation, weakening of the bad-row predicate, or change of row multiplicity occurs. The increment honestly discharges only semantic tagged-copy decomposition; it does not yet prove minimum/optimum value or fraction preservation, copied row cardinality, incidence preservation, a global tagged tuple law, or an encoded producer.

## Frozen artifacts and certification

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedFinite3LinSource.lean` | `D2145BA050CBE6772999B41F3B4027A82312D1A0387C1E0EDF00781C732F2956` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedFinite3LinSourceChecks.lean` | `936240D9DC71AD52427AAF7281FCBFC564D52A9865FAF3ED7ECBD2D43664E29D` |
| canonical `bundle-manifest.txt` | `47ECF28146B60515A89740BD915D81B0EA87CB0942E5EA68372DF08987FFA33B` |

The canonical evidence directory is `research/evidence/2026-09-15-tagged-finite-3lin-source-fresh-run/`. I independently recomputed the two source hashes, the manifest hash, and all 22 byte-count/hash entries in `bundle-manifest.txt`; every value matches. The before/after records show stable source hashes. Main and Checks exited `0` with empty stderr and emitted objects with hashes `CFC69AA8341AEE122687CE6B62551B0901C5664B454B2E4D160461F633B92FF7` and `E67EBA0C2645A4A06E07426EAE81A48B099877406E5941C837772E45B94DB75B`. The isolated target was seeded with the recorded 2,798 dependency outputs and lacked both reviewed objects before main-then-Checks compilation. This is a target-fresh certification of the two reviewed modules against pinned compiled dependencies, rather than a source rebuild of every dependency.

The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and user-declared `axiom` in both reviewed source files. The Checks transcript reports only `propext`, `Classical.choice`, and `Quot.sound` for all reviewed declarations. These are the ordinary Lean/Mathlib logical dependencies expected from finite sets, quotients, and extensional equality; no theorem-specific or unaccounted axiom appears. The compiler reports only unused-variable/style warnings.

The reviewed Lean files and evidence directory were untracked in the working tree at review time, above repository commit `d953c63d477574a3f9c85fe01e2704df774a43cf`. The hashes freeze the reviewed bytes, but this review does not supply commit provenance for them.

## Exact copied carrier

For a base source `I : Finite3LinSource Row Var`, `taggedCopy I K` uses row type `Fin K × Row` and variable type `Fin K × Var`, with

```text
row (k,q) i = (k, I.row q i)
rhs (k,q)   = I.rhs q.
```

The copied row injectivity proof is sound: equality of tagged variables gives equality of their second coordinates, and base row injectivity recovers equality of the two `Fin 3` positions. It introduces no cross-row injectivity assumption. Equal semantic base equations remain distinct whenever their `Row` identities are distinct, and different tags remain distinct through the first product coordinate.

`taggedCopy_row` and `taggedCopy_rhs` expose the construction definitionally. `taggedCopy_support` proves the exact finite-set identity

```text
support(taggedCopy I K, (k,q)) = image (v ↦ (k,v)) (support(I,q)).
```

The image map is injective because it fixes the first coordinate and retains `v` as the second coordinate. Thus the definition preserves the three distinct variables of each base row. The theorem also gives the needed representation for a later proof that supports with unequal tags are disjoint, but that cross-tag disjointness theorem is not itself present here.

## Bad-row correspondence and arbitrary-assignment decomposition

`restrictAssignment x k` is exactly `v ↦ x (k,v)`. Consequently

```text
(I.taggedCopy K).badRow x (k,q)
  = I.badRow (restrictAssignment x k) q
```

is definitional equality. It preserves the base predicate

```text
decide (¬(x(row q 0) + x(row q 1) + x(row q 2) = rhs q))
```

with the same negation, summand order, RHS, and Boolean-to-`Nat` indicator. There is no satisfaction/violation reversal or unstated consistency constraint between assignments on different tags.

After unfolding `violations`, `Fintype.sum_prod_type` rewrites the sum over `Fin K × Row` into the iterated sum over tags and rows. The remaining equality is definitional from `taggedCopy_badRow`. Therefore

```text
(I.taggedCopy K).violations x
  = ∑ k : Fin K, I.violations (restrictAssignment x k)
```

holds for every copied assignment, including assignments that differ arbitrarily between tags. It counts row identities with multiplicity and neither deduplicates equal equations nor averages over copies.

For `K = 0`, both row and variable carriers are empty. There is one function from the empty copied variable type to `ZMod 2`, the outer violation sum is empty, and the right-hand sum over `Fin 0` is empty, so the theorem states `0 = 0`. The proof does not require a nonexistent `k : Fin 0` and does not hide a positive-copy assumption.

## Repeated-assignment multiplication

`repeatAssignment x` discards the tag and returns `x v`. The theorem

```text
restrictAssignment (repeatAssignment x) k = x
```

is function extensionality with pointwise reflexivity. Rewriting the arbitrary-assignment decomposition therefore leaves a sum of the constant natural number `I.violations x` over `Fin K`; simplification gives

```text
(I.taggedCopy K).violations (repeatAssignment x)
  = K * I.violations x.
```

The factor is the cardinality of `Fin K`, and the multiplication is natural-number multiplication. No subtraction, division, cast, cancellation, or nonzero assumption is involved. At `K = 0`, the sum is empty and the right side is `0 * I.violations x = 0`; at `K = 1` it reduces to the base count; repeated multiplication for all larger `K` follows from the constant finite sum.

## Fixture audit

The Checks fixture `singleViolated` has one row on three distinct variables, RHS `1`, and proves that the zero assignment has exactly one violation. The repeated-assignment fixture at `K = 2` proves a copied total of `2`. The mixed assignment sets tag `0` to the zero assignment and at tag `1` sets only variable `0` to `1`; the first component violates and the second satisfies, so the proved copied total `1` exercises the arbitrary per-tag decomposition rather than only the repeated-assignment corollary.

These are proposition-level, kernel-checked examples. They cover a positive base violation, two-copy multiplication, and nonconstant cross-tag behavior. They do not include explicit `K = 0` or `K = 1` examples, support/cardinality examples, or a multiple-row base. This is not a proof gap: the generic theorems quantify over all `K`, and the `K = 0` case follows without a branch from empty finite sums. An explicit zero-copy fixture would strengthen regression presentation but would not add mathematical coverage.

## Scope and exact blockers

This increment completes the active bundle named in S3138 only through semantic construction, bad-row equivalence, violation-sum decomposition, and repeated-assignment multiplication. It does not define a minimum violation count, maximum satisfied count, optimum satisfaction value, or normalized violation/satisfaction fraction. In particular, repeated assignment proves only the upper-witness direction for a copied minimum. Exact optimum preservation still needs the converse lower bound obtained by applying base minimality separately to every restricted component of an arbitrary copied assignment.

There is no blocker to accepting the reviewed declarations. The exact blockers to calling tagged-copy padding or S3138 complete are:

1. Define the base and copied optimum objective and prove both directions of exact minimum/optimum preservation.
2. For normalized fractions, assume `0 < K` and a nonempty base row universe, prove `card (Fin K × Row) = K * card Row`, and justify the positive denominators before cancelling the common factor.
3. Prove row-count multiplication, support cardinality three, local incidence/degree preservation, pair-intersection preservation, and cross-tag support disjointness.
4. Specialize the semantic result to `Finite3LinSource.ofActual I` through `ofActual_violations`; do not introduce a disconnected copied-source value assumption.
5. Define the global independently tagged `J`-row product law and its projection. A one-tag mixture does not provide the required mass dilution.
6. Provide an encoded `tagCopiesFn`, decode correctness, output-size and runtime bounds, and an explicit polynomial bound on the chosen `K`.

None of retained good mass, conditioning, actual-star acceptance, a randomized reduction, hardness, P versus NP, manuscript completion, or publication readiness follows from this increment.

## Direct optimum consumer

The immediate consumer should define a finite minimum-violation objective and prove an exact theorem of the form

```text
minViolations (I.taggedCopy K) = K * minViolations I.
```

For the lower bound, take an arbitrary copied assignment `x`, use `taggedCopy_violations`, and bound every term `I.violations (restrictAssignment x k)` below by `minViolations I`. For the upper bound, choose a minimizing base assignment, repeat it, and use `taggedCopy_repeatAssignment_violations`. This proof is separability across tags; it must not assume that an optimum copied assignment repeats one base assignment.

The route-level consumer should then prove, under `0 < K` and `0 < Fintype.card Row`, equality of copied and base optimum violation fractions, and hence of satisfaction fractions, using the row-cardinality product. The actual-source specialization should rewrite with `Finite3LinSource.ofActual_violations` and `rowId_card_eq_rows_length`. That specialization is the direct bridge from this semantic decomposition to the S3138 source-value obligation.

## Disposition

**GO-WITH-NOTES.** The exact statements are sound, the certification and axiom evidence match the frozen bytes, arbitrary copied assignments decompose correctly, repeated assignments multiply violations correctly for every natural `K`, and the empty-copy edge case is valid. The notes are scope boundaries and downstream obligations. This review accepts semantic tagged-copy decomposition only and does not close optimum preservation or S3138.
