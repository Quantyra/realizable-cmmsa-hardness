# Finite 3-LIN optimum: non-claims-boundary review

2026-09-15. Read-only review of the frozen `Finite3LinOptimum` increment, its Checks module, and the routed fresh-run evidence. No Lean source, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment defines the semantic minimum violation count of a finite 3-LIN source and proves that a `K`-tagged copy has exactly `K` times the base minimum violation count. It defines the normalized minimum violation rate and `value := 1 - minimumViolationRate`, then proves preservation of both quantities when `0 < K` and the base row type is nonempty.

This verdict authorizes only the semantic minimum-count, normalized-rate, and defined-value wording below. It does not certify a source producer, encoding or runtime bound, global independently tagged tuple law, manuscript parameter identification, retained mass, conditioning result, hardness consequence, P-versus-NP consequence, novelty, or publication readiness.

## Frozen artifacts and certification evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/Finite3LinOptimum.lean` | `A4FD9733CB93D08E04D1091F07F27C359CA1F16A12E487FC3D40F43F1558E6D2` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/Finite3LinOptimumChecks.lean` | `EBDDBBC5EB1277A54E60CDF843AE0FFB4FF1FEC307A83625F99EF1EB46C25A9F` | Matches the routed freeze. |
| `research/evidence/2026-09-15-finite-3lin-optimum-fresh-run/bundle-manifest.txt` | `536F9F5CCE3B6CB1DA79B9C1FCA84B735E3F377DC10DA2B0719E8BF050C91485` | Matches the routed evidence-manifest hash. |

The bundle records unchanged before/after source hashes, final main and Checks exit codes `0`, empty final stderr, and emitted object hashes `596EFBD09A22810D69BCAE0A90EBCF589131A98854336F666131860BDC23C71D` and `492091452AFA9FFF65D12B215F5440B206F5B0F8B28CB6A543361E36E6DDF538`. The final target seeded Checks attempt succeeded after three preserved setup failures. Those failures concern `LEAN_PATH` construction, not a rejected theorem or fixture.

The recorded forbidden-token scan has no matches, and an independent read-only scan of the two frozen files likewise found no `sorry`, `admit`, `native_decide`, or source-level `axiom`. The Checks transcript reports only `[propext, Classical.choice, Quot.sound]` for the reviewed declarations. These are ordinary Lean/mathlib foundations here; no project-specific axiom is reported.

The target directory was fresh for the main target, while dependency objects were copied into it before the successful Checks compile. The evidence therefore certifies direct compilation of the two frozen files against recorded seeded dependencies. It is not evidence of a clean rebuild of every transitive dependency.

## Exact theorem boundary

For a finite source `I : Finite3LinSource Row Var`, the increment defines

`I.minViolations := min { I.violations x | x : Var -> ZMod 2 }`.

The finite assignment space is nonempty, including when `Var` is empty, so the minimum exists. The proved interface establishes:

- `minViolations_le_violations`: the minimum is at most the violation count of every assignment;
- `exists_violations_eq_minViolations`: some assignment attains the minimum;
- `taggedCopy_minViolations`: for every natural `K`, including `K = 0`, `(I.taggedCopy K).minViolations = K * I.minViolations`;
- `minimumViolationRate`: the real-valued quotient `minViolations / card Row`;
- `value`: the defined quantity `1 - minimumViolationRate`;
- `taggedCopy_minimumViolationRate`: exact preservation under `0 < K` and `0 < card Row`;
- `taggedCopy_value`: exact preservation under the same two positivity hypotheses.

The count theorem has no positivity premise and covers the empty tagged copy. The normalized theorem deliberately requires a positive copy count and nonempty base row type, allowing cancellation of the common factor `K` in the numerator and row cardinality. The `value` theorem is a direct consequence of the normalized-rate theorem and uses the module's explicit definition of `value`.

The minimum-count proof supplies both optimization directions: repeating a base minimizer gives the copied upper bound, while restricting an arbitrary copied minimizer to each tag and summing the base lower bound gives the copied lower bound. This is exact semantic optimum preservation for the tagged-copy construction already defined in `TaggedFinite3LinSource`; it is not a claim about an encoded instance producer or about any probabilistic question-generation process.

## Fixture audit

The Checks fixture defines `contradictoryTwoRow`, a two-row, three-variable semantic source whose two rows use the same three coordinates and opposite right-hand sides. Consequently every assignment violates exactly one of the two rows. The fixture proves the base minimum is `1` and checks:

- the zero-copy minimum is `0`;
- the three-copy minimum is `3`;
- the base minimum violation rate is `1/2`;
- the three-copy minimum violation rate is `1/2`;
- the base defined value is `1/2`;
- the three-copy defined value is `1/2`.

This is a non-vacuous check of the intended minimum, scaling, normalization, and value behavior, plus the `K = 0` edge case for the unnormalized count. It does not test a zero-row base source, and it does not extend the normalized preservation theorem beyond its explicit positivity hypotheses. It also supplies no producer, distribution, retained-mass, or complexity evidence.

## Permitted wording

The strongest justified description is:

> Lean defines the minimum number of violated rows over all assignments of a finite semantic 3-LIN source. For its semantic `K`-tagged copy, the minimum violation count is exactly `K` times the base minimum for every natural `K`. When `K` is positive and the base row type is nonempty, the normalized minimum violation rate and the defined value `1 - minimumViolationRate` are preserved exactly.

Acceptable shorter descriptions are "semantic minimum-violation scaling under tagged copy," "normalized minimum-violation-rate preservation under positive, nonempty hypotheses," and "preservation of the module's defined 3-LIN value under tagged copy." Any use of "optimum" or "value preservation" must identify the semantic `Finite3LinSource` quantity and retain the positivity hypotheses for normalized statements.

Do not describe this increment as proving or certifying:

- an encoded, computable, polynomial-time, or output-size-bounded tagged-copy producer;
- a global independently tagged `J`-tuple law or any sampler/distribution identity;
- the manuscript's `N_outer`, a retained-good-mass bound, positive retained mass, or a conditioning guarantee;
- expansion, collision control, star acceptance, a completed reduction, approximation hardness, or any hardness result;
- P versus NP, circuit or proof-system lower bounds, or another complexity separation;
- novelty, manuscript correctness, publication readiness, or route-final completion.

## Material notes

1. The theorem and fixture stay within the requested semantic minimum-count, normalized-rate, and defined-value boundary.
2. The normalized preservation statements require both `0 < K` and `0 < card Row`; the unnormalized scaling theorem alone may be stated at `K = 0`.
3. Calling the defined quantity `value` is accurate when tied to the module definition. Broader uses such as game value, acceptance probability, or reduction value require separate bridges.
4. The certification evidence is adequate for the frozen two-file increment, with its seeded-dependency scope stated above.
5. No public-claim promotion follows from this review.
