# Finite 3-LIN optimum: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for S3138

## Verdict

**GO-WITH-NOTES for the frozen generic semantic optimum increment.**

The reviewed Lean declarations establish the exact minimum violated-row count of a tagged disjoint union and, under the stated positive-copy and nonempty-row hypotheses, exact preservation of the normalized minimum violation rate and its complementary value. Both directions of the optimum argument are present. This is the force-bearing semantic value theorem that the preceding tagged-copy decomposition increment lacked.

The result closes the generic semantic optimum/value-preservation step of S3138. It does not close S3138 as a route: there is no named actual-source specialization, encoded polynomial producer, structural copied-incidence package, global independently tagged `J`-tuple law, explicit `N_outer` interface, retained-mass theorem, conditioning theorem, or hardness assembly in this increment.

## Frozen artifacts and evidence

| Artifact | Reviewed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/Finite3LinOptimum.lean` | `A4FD9733CB93D08E04D1091F07F27C359CA1F16A12E487FC3D40F43F1558E6D2` | Exact requested frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/Finite3LinOptimumChecks.lean` | `EBDDBBC5EB1277A54E60CDF843AE0FFB4FF1FEC307A83625F99EF1EB46C25A9F` | Exact requested frozen Checks source. |
| `research/evidence/2026-09-15-finite-3lin-optimum-fresh-run/bundle-manifest.txt` | `536F9F5CCE3B6CB1DA79B9C1FCA84B735E3F377DC10DA2B0719E8BF050C91485` | Exact requested manifest; all 38 listed entries independently rehashed with zero mismatches. |

The evidence records final main/Checks exits `0/0`, empty final stderr, unchanged before/after source hashes, and object hashes `596EFBD09A22810D69BCAE0A90EBCF589131A98854336F666131860BDC23C71D` and `492091452AFA9FFF65D12B215F5440B206F5B0F8B28CB6A543361E36E6DDF538`. The forbidden scan for `sorry`, `admit`, `native_decide`, and source-level `axiom` is empty. The emitted axiom profiles contain only the standard inherited `propext`, `Classical.choice`, and `Quot.sound`.

The target was fresh for the reviewed main object. The successful Checks run used the newly emitted main object plus copied dependency objects from the recorded prior tagged-source seed. Three failed Checks path/setup attempts are retained transparently and do not weaken the final successful certification. This is target-fresh certification of the two frozen modules against recorded cached dependencies, not a clean rebuild of the full transitive dependency graph.

## Exact theorem content

For any finite `Finite3LinSource Row Var`, `minViolations` is the minimum of the finite image of the assignmentwise violation-count function. The assignment space is nonempty even when `Var` is empty, so the minimum exists without a `Nonempty Var` premise. The module proves:

1. `minViolations_le_violations`: the defined minimum is at most the violation count of every assignment.
2. `exists_violations_eq_minViolations`: some assignment attains the minimum.
3. `taggedCopy_minViolations`:

   ```text
   minViolations(taggedCopy I K) = K * minViolations(I)
   ```

   for every natural `K`, including `K = 0`.
4. `taggedCopy_minimumViolationRate`: if `0 < K` and `0 < card Row`, then

   ```text
   minViolations(taggedCopy I K) / card(Fin K x Row)
     = minViolations(I) / card Row.
   ```

5. `taggedCopy_value`: under the same hypotheses, the complementary value `1 - minimumViolationRate` is exactly preserved.

The count proof contains both necessary optimum directions. Repeating a minimizing base assignment proves the copied optimum is at most `K` times the base optimum. Conversely, an arbitrary minimizing copied assignment restricts to `K` base assignments; base minimality applied to each restriction and the previously certified violation-sum decomposition prove the lower bound. Thus this is not merely a repeated-witness upper bound.

Here `value` is defined to be the complement of the minimum violation rate. For a nonempty row carrier this is the usual optimum satisfied-row fraction, because every row is either violated or satisfied. The reviewed module does not separately define a maximum satisfied-row count or prove that characterization; its exact preservation claim is nevertheless fully established for the stated `value` definition.

The two-row contradictory fixture is mathematically nonvacuous: it proves base minimum `1`, copied minimum `3` for `K = 3`, base and copied minimum violation rate `1/2`, and base and copied value `1/2`. It also checks the count theorem at `K = 0`.

## Positivity audit

The assumptions are safe and sufficient, with the following sharp distinctions.

- `taggedCopy_minViolations` needs neither `0 < K` nor `0 < card Row`. At `K = 0`, the copied carrier has no rows and its minimum violation count is zero, matching `0 * minViolations(I)`.
- For a uniform theorem over nonempty base systems, `0 < K` is necessary for rate/value preservation. With `K = 0` and the contradictory fixture, the copied violation rate is Lean's `0 / 0 = 0`, while the base rate is `1/2`.
- `0 < card Row` is the correct hypothesis for interpreting the quotient as an ordinary normalized row fraction and is what permits direct cancellation in the current proof. It is stronger than logically necessary for the bare equality as Lean defines division: when `card Row = 0`, every violation count and minimum is zero, so both rates are zero and both values are one for every `K`, including `K = 0`. The current theorem is therefore conservative rather than unsound.
- No positivity or nonemptiness premise on `Var` is needed.
- For an actual source `I : ActualOccurrenceAllocation.Instance N m`, the accepted identities

  ```text
  card I.RowId = I.rows.length
  m <= I.rows.length
  ```

  give `0 < card I.RowId` from the standard source hypothesis `0 < m`. The existing `rows_length_pos` theorem provides the intermediate positivity directly.

## Consequence for S3138 and actual-source specialization

The generic theorem can be instantiated immediately with `Finite3LinSource.ofActual I`. Given `0 < K` and `0 < card I.RowId`, it yields

```text
value ((Finite3LinSource.ofActual I).taggedCopy K)
  = value (Finite3LinSource.ofActual I),
```

and the analogous exact minimum-violation-rate equality. Together with `Finite3LinSource.ofActual_violations`, the base semantic carrier counts exactly the violations of the actual post-regularization row/RHS system for every assignment. Thus no approximation loss is introduced by tagged copying at this semantic level.

This consequence is presently an instantiation path, not a named theorem in an actual-source module. The increment also does not define an optimum or value directly on `ActualOccurrenceAllocation.Instance`, nor prove an explicit equality between such an actual-instance definition and `value (ofActual I)`. A route-facing specialization should package the hypotheses from `0 < m`, rewrite the denominator with `rowId_card_eq_rows_length`, and expose the exact copied actual-source value theorem consumed by later modules.

The result preserves the value of the **post-regularization semantic source**. It does not prove exact optimum equality between the raw upstream source and the regularized source. Existing regularization completeness and soundness statements remain subject to their own hypotheses and scaling; they must be transported separately.

Accordingly, S3138 may mark its generic exact optimum/fraction-preservation obligation complete, while the story remains **Active** under its stop-loss until the global tuple law and the other route obligations below are discharged.

## Obligations not discharged by this increment

### Encoded polynomial producer

The construction remains a noncomputable finite-type semantic object. No encoded `tagCopiesFn`, decoding-correctness theorem, output-size bound, running-time bound, or membership in the repository's FP model occurs here. Complexity remains linear in `K` only as an informal representation expectation; the route still must show that the chosen `K` is fixed or polynomially bounded and computable from the encoded input and that the same encoded producer realizes the reviewed semantic copy.

### Structural incidence

The theorem uses the tagged semantic carrier and violation decomposition but proves no copied support-size-three theorem, incidence-degree-at-most-four theorem, same-tag pair-intersection theorem, or cross-tag support-disjointness theorem. These facts are expected from the product construction, but the actual-source structural bounds do not automatically become exported theorems about the copied carrier. Plain disjoint copying also creates disconnected components, so no expansion or random-walk property follows.

### Global independent `J`-tag law

No probability or tuple-law declaration occurs. The required global sample space is

```text
Fin J -> (Fin K x Row),
```

with tags sampled independently across coordinates, equivalently the product decomposition into `(Fin J -> Fin K)` and `(Fin J -> Row)`. The one-common-tag mixture law is still invalid for the intended dilution argument. Exact optimum preservation is deterministic and does not establish any sampling independence, pushforward, marginal, or collision bound.

### `N_outer`

The imported product carrier makes the cardinality identity

```text
card (Fin K x Row) = K * card Row
```

available at the library level, and with `Row = I.RowId` and `rowId_card_eq_rows_length` the intended copied count is `K * I.rows.length`. This increment does not state the route-facing theorem or identify that number with the manuscript's `N_outer`. It must remain distinct from raw variable count `N`, raw equation count `m`, and base post-regularization row count `I.rows.length`.

### Retained mass and conditioning

No choice of positive `K`, bad-mass ratio bound, positive good/retained mass, conditioning legality, conditioned marginal, ordered-to-subset transport, or star acceptance theorem is proved. The optimum theorem supplies no such probabilistic consequence by itself.

### Hardness and headline

The increment does not provide the upstream hard encoded source, an efficient reduction, YES/NO promise transport through all stages, soundness amplification, randomized many-one hardness, a learning lower bound, or a P-versus-NP conclusion. It supports no public headline beyond the exact scoped statement: **tagged disjoint copies preserve the minimum violation fraction and complementary semantic value of a finite 3-LIN source under positive copy count and nonempty row carrier.**

## Acceptance boundary

Accept the frozen declarations as exact generic semantic optimum/value preservation. Do not describe this review as completing source-preserving padding as an algorithmic or probabilistic reduction. S3138 remains open until the actual route-facing specialization, copied structural package, encoded polynomial producer, independent global `J`-tag law, explicit `N_outer` bridge, and positive retained-mass/conditioning chain are certified. No hardness or headline promotion follows from this verdict.
