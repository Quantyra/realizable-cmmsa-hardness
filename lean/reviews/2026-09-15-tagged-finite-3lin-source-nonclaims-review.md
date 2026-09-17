# Tagged finite 3-LIN source: non-claims-boundary review

2026-09-15. Read-only review of the frozen `TaggedFinite3LinSource` increment, its Checks module, and the routed fresh-run evidence. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment constructs a semantic tagged copy of a `Finite3LinSource` on row type `Fin K × Row` and variable type `Fin K × Var`. It proves exact coordinate, right-hand-side, support, row-badness, assignment-restriction, and total-violation decomposition facts. It also proves the repeated-assignment violation count `K * I.violations x`.

This verdict authorizes only the semantic tagged-copy/decomposition wording stated below. The increment does not prove optimum equality, a polynomial producer, a global independently tagged `J`-tuple law, expansion, retained good mass, hardness, P versus NP, novelty, or publication readiness.

## Frozen artifacts and certification evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedFinite3LinSource.lean` | `D2145BA050CBE6772999B41F3B4027A82312D1A0387C1E0EDF00781C732F2956` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedFinite3LinSourceChecks.lean` | `936240D9DC71AD52427AAF7281FCBFC564D52A9865FAF3ED7ECBD2D43664E29D` | Matches the routed freeze. |
| `research/evidence/2026-09-15-tagged-finite-3lin-source-fresh-run/bundle-manifest.txt` | `47ECF28146B60515A89740BD915D81B0EA87CB0942E5EA68372DF08987FFA33B` | Matches the routed evidence-manifest hash. |

The evidence records main and Checks exit codes `0`, empty stderr, unchanged before/after source hashes, and emitted object hashes `CFC69AA8341AEE122687CE6B62551B0901C5664B454B2E4D160461F633B92FF7` and `E67EBA0C2645A4A06E07426EAE81A48B099877406E5941C837772E45B94DB75B`. The forbidden-token scan is clean for `sorry`, `admit`, `native_decide`, and source-level `axiom`. The Checks transcript reports no axioms for `restrictAssignment` and `repeatAssignment`; the other reviewed declarations report only `[propext, Classical.choice, Quot.sound]`.

The target was seeded from the prior `actual-finite-3lin-source-fresh-20260915` object inventory. The preflight records `False` for `Test-Path` on both target objects before compilation, and the final inventory contains both newly emitted objects. This certifies fresh compilation of the two frozen targets against recorded cached dependencies. It is not evidence of a clean rebuild or independent revalidation of every transitive dependency. The `terminal.json` field name `output_objects_absent_precompile` is misleading because its stored `false` values are the raw precompile existence checks; `preflight.txt`, the commands, and the inventory make the intended interpretation recoverable.

## Exact theorem boundary

For `I : Finite3LinSource Row Var` and `K : Nat`, `taggedCopy` defines:

- copied rows as `(k, q) : Fin K × Row`;
- copied variables as `(k, v) : Fin K × Var`;
- row coordinates as `(k, I.row q i)`;
- copied right-hand sides as `I.rhs q`.

The proved interface establishes:

- `taggedCopy_row`: exact tagged coordinate transport;
- `taggedCopy_rhs`: exact right-hand-side transport;
- `taggedCopy_support`: support is the image of the base support under the fixed tag `k`;
- `taggedCopy_badRow`: copied-row badness under `x` equals base-row badness under the tag-restricted assignment;
- `restrictAssignment_repeatAssignment`: restricting a repeated assignment returns the base assignment;
- `taggedCopy_violations`: total copied violations decompose as the sum of base violations over tags;
- `taggedCopy_repeatAssignment_violations`: a repeated base assignment incurs exactly `K` times its base violation count.

These are assignmentwise semantic identities. They do not take a minimum or maximum over assignments. Although the restriction and repetition maps are ingredients one could use in a later optimum argument, the reviewed module contains no optimum definition and no optimum-equality theorem. In particular, the repeated-assignment theorem supplies one explicit class of copied assignments; it must not be quoted as optimum preservation.

The row and variable product types make different tags definitionally distinct, but the module does not state the additional structural and quantitative interfaces that downstream claims may require. It proves no explicit row-count multiplication theorem, variable-degree theorem, pair-intersection theorem, expansion statement, encoding-size bound, runtime bound, or producer correctness theorem. At `K = 0`, both copied types are empty, so any future normalized-value or positive-copy argument must state and use its own positivity hypothesis.

## Fixture audit

The Checks fixture defines a one-row source with identity coordinates and right-hand side one. It certifies proposition-level examples showing:

1. the zero base assignment violates the single row once;
2. repeating that assignment across two tags gives two violations;
3. a mixed two-tag assignment, with one violating restriction and one satisfying restriction, gives one total violation.

The fixture is a useful concrete check of repetition and nonuniform-tag decomposition. It does not compute an optimum, test `K = 0`, certify a producer, sample independently tagged tuples, establish expansion or retained mass, or connect the semantic carrier to a hardness reduction. No native evaluation is used.

## Exact wording limits

The strongest justified description is:

> Lean defines a semantic `K`-tagged copy of a finite 3-LIN source, tags each row variable within its copy, preserves each copied right-hand side, identifies copied support and row badness under tag restriction, and decomposes total violations as the sum of the base-source violations induced by each tag-restricted assignment. Repeating one base assignment across all tags yields `K` times its base violation count.

Acceptable shorter descriptions are “semantic tagged-copy construction,” “assignmentwise violation decomposition across tags,” and “repeated-assignment violation scaling.” Any use of “copy” must identify this as the semantic `Finite3LinSource` construction and must not imply a certified encoded instance producer or runtime bound.

Do not describe this increment as proving or certifying:

- optimum violation or satisfaction equality, value preservation, or approximation preservation;
- a polynomial-time or output-size-bounded producer;
- a global independently tagged `J`-tuple distribution or law;
- expansion, collision control, conditioning, retained good mass, or positive retained mass;
- a completed reduction, hardness, P versus NP, or any other complexity separation;
- novelty, manuscript correctness, publication readiness, or route-final completion.

## Material notes

1. The declarations and fixture stay within the intended semantic tagged-copy/decomposition boundary.
2. The fixture exercises both repeated and tag-varying assignments, but it supplies no optimization or distributional evidence.
3. The certification is adequate for the frozen two-file increment, with the seeded-dependency and `terminal.json` field-name caveats stated above.
4. Any downstream theorem about normalized source value needs a positive copy count and a separate optimum argument in both directions.
5. No public-claim promotion follows from this review.
