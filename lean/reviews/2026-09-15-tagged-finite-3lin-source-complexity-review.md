# Tagged finite 3-LIN source: complexity-theory review

Date: 2026-09-15  
Review mode: read-only complexity-theory lens under Source-preserving tagged-copy padding (S3138)

## Verdict

**GO-WITH-NOTES** for the frozen semantic tagged-copy and assignmentwise violation-decomposition increment.

The construction is an honest disjoint union of `K` copies at the semantic finite-3-LIN level: both rows and variables carry the same copy tag, copied right-hand sides are unchanged, copied row badness is exactly base-row badness under the tag-restricted assignment, and total violations are the sum of the component violation counts. This is useful force-bearing infrastructure for the next exact optimum proof.

The increment does **not** yet establish optimum violation-count equality, normalized value preservation, an encoded polynomial producer, the global independently tagged tuple law, the manuscript identification of `N_outer`, or positive retained mass. It therefore does not close S3138 and cannot support conditioning, star acceptance, hardness, or headline consequences.

## Frozen artifacts and evidence

| Artifact | Reviewed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedFinite3LinSource.lean` | `D2145BA050CBE6772999B41F3B4027A82312D1A0387C1E0EDF00781C732F2956` | Matches the requested frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedFinite3LinSourceChecks.lean` | `936240D9DC71AD52427AAF7281FCBFC564D52A9865FAF3ED7ECBD2D43664E29D` | Matches the requested frozen Checks source. |
| `research/evidence/2026-09-15-tagged-finite-3lin-source-fresh-run/bundle-manifest.txt` | `47ECF28146B60515A89740BD915D81B0EA87CB0942E5EA68372DF08987FFA33B` | Matches the requested evidence manifest; all 22 listed entries were rehashed successfully. |

The evidence records sequential main/Checks exits `0/0`, unchanged source hashes, empty stderr, and emitted object hashes `CFC69AA8341AEE122687CE6B62551B0901C5664B454B2E4D160461F633B92FF7` and `E67EBA0C2645A4A06E07426EAE81A48B099877406E5941C837772E45B94DB75B`. The forbidden scan for `sorry`, `admit`, `native_decide`, and source-level `axiom` is empty. The reported dependencies are the standard inherited `propext`, `Classical.choice`, and `Quot.sound`, except that the two assignment maps report no axioms.

The target was seeded from the prior actual-finite-source dependency target, while the two reviewed target objects were absent before compilation. Thus the evidence certifies fresh emission of these two frozen modules against recorded cached dependencies, not a clean rebuild of every transitive dependency. In `terminal.json`, `output_objects_absent_precompile` stores `false`; the preflight shows these are raw `Test-Path` results, so the field name is misleading but the underlying evidence is recoverable.

## What is exactly established

For every finite source `I : Finite3LinSource Row Var` and natural `K`, `I.taggedCopy K` has row type `Fin K × Row` and variable type `Fin K × Var`, with

```text
row (k,q) i = (k, I.row q i)
rhs (k,q)   = I.rhs q.
```

The following semantic facts are kernel-checked:

1. `taggedCopy_row` and `taggedCopy_rhs` expose the exact coordinate and RHS definitions.
2. `taggedCopy_support` identifies a copied row's support with the image of the base support under the fixed tag `k`.
3. `taggedCopy_badRow` proves exact bad-row equivalence after restricting the copied assignment to tag `k`.
4. `restrictAssignment_repeatAssignment` proves that restricting a repeated base assignment returns the base assignment.
5. `taggedCopy_violations` proves, for an arbitrary copied assignment `x`,

   ```text
   violations(taggedCopy I K, x)
     = sum over k : Fin K of violations(I, restrictAssignment x k).
   ```

6. `taggedCopy_repeatAssignment_violations` proves that repeating one base assignment gives exactly `K * I.violations x` copied violations.

The fixture is nonvacuous at the assignmentwise level. Its one-row base system has one violation under the zero assignment; the repeated assignment over two tags has two violations; and a mixed assignment with one satisfying and one violating tag has one violation. This confirms that the decomposition is not restricted to repeated assignments.

The product carriers make variables from different tags distinct. Accordingly, each copied component can be assigned independently. The module does not separately prove row-cardinality multiplication, support-cardinality preservation, degree preservation, same-tag pair-intersection preservation, or cross-tag disjointness as downstream interfaces.

## Optimum and value boundary

No optimum, minimum-violation count, satisfaction fraction, or normalized value is defined in the reviewed module. No theorem takes a minimum or maximum over assignments. Therefore exact value preservation is **not yet a certified result** of this increment.

The two required inequalities are visible but remain to be formalized. If `u(I)` denotes the minimum number of violated rows, then:

- repeating a minimizing base assignment gives `u(taggedCopy I K) ≤ K * u(I)`;
- the violation decomposition, together with base optimality applied separately to every restricted tag assignment, gives `K * u(I) ≤ u(taggedCopy I K)`.

`taggedCopy_repeatAssignment_violations` alone supplies only the witness direction. The arbitrary-assignment decomposition supplies the main lower-bound ingredient, but the bundle still lacks the finite optimizer/minimum interface and the equality theorem. It must not be described as value preservation until those are present and reviewed.

The assumptions should be kept sharp in the next proof:

- Exact **minimum violation-count multiplication** can be stated for every `K`, including `K = 0`, once the minimum over the finite assignment space is defined. At `K = 0`, the copied row and variable carriers are empty and both sides of the count identity are zero.
- Exact **normalized violated/satisfied fraction preservation** needs `0 < K` and `0 < Fintype.card Row`, equivalently a nonempty base row type, so both base and copied denominators are positive and the factor `K` can be cancelled.
- The assignment space needs no extra nonempty-variable hypothesis: even when `Var` is empty, `Var → ZMod 2` is inhabited by the zero function. Finiteness of `Var` and the finite codomain suffice for optimizer existence. If the chosen library minimum API asks for nonemptiness, the relevant nonempty object is the assignment space, which can be constructed without assuming `Nonempty Var`.
- A proof that selects a concrete copy tag also needs `0 < K`; the cleaner sum-of-component-optima lower bound does not require selecting one tag and continues to cover `K = 0`.

These points separate the combinatorial count theorem from the ratio theorem and prevent an empty-denominator case from being hidden in a generic value definition.

## Does copying preserve the source law?

At the local CSP semantic level, copying does not alter the equation within a component: the three variables receive the same tag, the RHS is identical, and satisfaction under a copied assignment is exactly satisfaction under its tag restriction. Thus each tag induces an isomorphic copy of the base row/RHS system, and the attainable component assignments are independent because the variable sets are disjoint.

Copying nevertheless changes the sample carrier from `Row` to `Fin K × Row`. For `K > 0` and a nonempty `Row`, a uniformly sampled tagged row has a uniform tag and a uniform base-row projection, so the projected one-row law should equal the uniform base-row law. That distributional statement is not proved here.

For `J` rows, the required manuscript law is uniform sampling from

```text
Fin J → (Fin K × Row),
```

equivalently independent uniform tag and base-row functions at every coordinate. It is not the law that first chooses one tag and then samples all `J` base rows inside that single component. The latter common-tag mixture has no `K`-fold dilution of cross-coordinate conflict mass. No tuple-space bijection, pushforward equality, normalization theorem, or independence theorem occurs in this increment.

Nor does the semantic carrier prove that copying preserves an upstream random-instance producer law or that raw occurrence regularization commutes with copying. The construction deliberately copies the post-regularization `Finite3LinSource`; it does not copy a raw `ActualOccurrenceAllocation.Instance`. Any claim about the original source distribution, serialization, or producer must use a separate exact bridge. Plain disjoint copies also destroy connectedness across components, so no expansion or random-walk property follows.

## Remaining route obligations

### Encoded producer

Define one encoded `tagCopiesFn` for the exact copied semantic system and prove decode correctness for rows, tagged variables, and RHS values. Prove membership of that same function in the repository's FP model and bound its serialized output by `O(K * size(I))` with encoding overhead made explicit. Polynomiality requires the selected `K` to be fixed by manuscript parameters or proved polynomially bounded and computable from the encoded input. The current noncomputable `Fintype` construction gives no runtime, uniformity, or output-size result.

### Global tuple law

Prove the finite equivalence

```text
(Fin J → Fin K × Row)
  ≃ (Fin J → Fin K) × (Fin J → Row)
```

and its uniform-measure/product-law consequence. The theorem must show independent tags across coordinates and the correct uniform base-row projection. The statement needs positive cardinalities wherever normalized probabilities divide by `K`, `card Row`, or their powers. It should be connected explicitly to the question sampler actually consumed by the star construction.

### `N_outer`

Prove

```text
Fintype.card (Fin K × Row) = K * Fintype.card Row.
```

For `Row = I.RowId`, combine this with the accepted bridge

```text
Fintype.card I.RowId = I.rows.length.
```

The manuscript's copied outer universe should therefore use

```text
N_outer = K * I.rows.length,
```

if `N_outer` denotes the copied sampled row universe, or explicitly distinguish the base outer size `I.rows.length` from the copied size. Neither quantity may be silently identified with the raw variable count `N` or raw equation count `m`; the regularized row list has its own cardinality. An exact notation/interface theorem is still required.

### Structural and retained-mass bridge

Prove copied support size three, variable incidence degree at most four, preservation of same-tag row intersections/conflicts, and disjointness across different tags. Then instantiate the generic ordered-question count/mass bound on the copied row universe rather than assuming the existing actual-instance specialization applies automatically.

Choose an explicit positive integer `K` satisfying the manuscript tolerance, for example by proving the certified bad-mass bound is at most `min(tau / 100, 1 / 4)` under the exact parameter hypotheses. Establish positive copied row cardinality and a strictly positive lower bound on good/retained mass before defining or using conditioning. Only after the independently tagged global law and positive retained mass are proved can the route address conditioned marginals, ordered-to-subset transport, star/clique acceptance, or repetition soundness.

### Source-value and hardness transport

After the abstract optimum theorem, instantiate it at `Finite3LinSource.ofActual I` using `ofActual_violations`. Keep the existing distinction between exact semantic conversion and the conditional completeness/soundness guarantees of actual regularization. The tagged-copy theorem does not supply the upstream hardness producer, exact raw-to-regularized optimum equality, or the final randomized reduction.

## Complexity-theory boundary

This increment supplies real semantic infrastructure rather than a false force claim: the arbitrary-assignment sum identity is exactly the ingredient needed for the missing lower direction of the optimum proof. Its force stops at assignmentwise copied violation counts. It gives no value theorem, distribution theorem, retained-mass theorem, expansion property, efficient transformation, approximation hardness, P-versus-NP consequence, novelty result, or publication claim.

S3138 should remain active until exact normalized value preservation, the encoded producer, and the global independently tagged tuple law are certified. Conditioning and claim-facing use must remain blocked until the `N_outer` and positive-retained-mass obligations are also discharged.
