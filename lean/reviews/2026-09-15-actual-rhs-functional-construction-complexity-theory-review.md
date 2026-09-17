# Actual RHS-functional construction: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for the S3138 actual-star algebraic bridge  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment proves the intended finite-linear-algebra obligation. For a good question `U` whose rows have three coordinates, the row-incidence vectors are linearly independent over `ZMod 2`. Consequently, every supplied RHS assignment induces exactly one linear functional on the span of those equation vectors. The actual-source wrapper specializes this statement to `I.support` and `I.rowRhs`, and the dimension theorem identifies the equation-span finrank with `U.card`.

This is sufficient to discharge the previously open construction of the equation-span functional used as `g` by the certified side-condition agreement theorem. It does not yet construct the coordinate-space functional `f`, extend or glue the two functionals, define label transport, or prove actual-star acceptance. The proof is noncomputable and contains no running-time statement, so it must not be treated as an efficient reduction component.

No complexity, PCP, satisfiability, soundness, hardness, or randomized-reduction premise is present in the four theorem signatures. The only source-specific facts used by the actual wrapper are the actual incidence representation's three-coordinate support theorem and the `GoodQuestion` premise. The result neither assumes nor proves that the full source system is satisfiable.

## Frozen artifacts and evidence

The reviewed Lean commit is `0ae4103373c1848a8ed6980cbca63784ab3a7025` (`prove actual rhs functional construction`).

| Artifact | Independently observed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualRhsFunctionalConstruction.lean` | `A38112D36CED08F6D8AD151D85D08D1140CD8A17D40EFED8DEAB6B25E3100428` | Matches the frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualRhsFunctionalConstructionChecks.lean` | `59CD64CCACDE1E2F3BB286A600939187FD5C5DC93024BAB11DBB1F0E1A1DCB9B` | Matches the frozen Checks source. |
| `research/evidence/2026-09-15-actual-rhs-functional-construction-fresh-run/artifact-hashes.txt` | `6DCE57B5372EEEEA857AC23C93662F5B6B64F7ABF520CCBE40BEC33C93163E3C` | Matches the evidence pointer and independent rehash record. |
| `research/evidence/2026-09-15-actual-rhs-functional-construction-closeout.md` | `50FAE722706AF678BA7AEA26EBAFF38111FF7A83C899831D116C960CE398F5D2` | Certification receipt reviewed. |
| `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md` | `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240` | Manuscript version assessed, especially the star-construction contract at lines 171--187. |

The certification rebuilt the frozen support, span-intersection, and finite-source dependencies and then compiled the frozen main and Checks modules sequentially with Lean `4.34.0-rc2` and `LEAN_NUM_THREADS=1`; all five stages exited zero. The isolated target contained none of those five objects before compilation. The resulting main and Checks object hashes are `9A8526B28F205FD8153F9E43FB3A36DF374E6BADB4F7091C9C9721AFDA9D650F` and `C46CFA10CD02A6F1E32B5B8F3B0AF359C413577D17633DD2BD1D05CB389636FF`. The 36-row evidence inventory independently rehashed with zero discrepancies, and the sources remained stable.

This is a target-fresh direct-project-dependency rebuild against hashed transitive objects, not a from-source rebuild of Mathlib and the complete repository graph. The forbidden scan is clean for `sorry`, `admit`, `native_decide`, `span_induction`, and explicit source-level axiom declarations. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for all four reviewed theorems.

## Exact claims and assumption audit

`equationVectors_linearIndependent` assumes pairwise-disjoint row supports within `U` and nonemptiness of each selected row. It isolates the coefficient of a selected row by evaluating the linear combination at one coordinate in that row; disjointness makes every other selected row vanish there. This is exactly the needed argument over `ZMod 2`. It does not use the stronger no-cross-row part of `GoodQuestion`, and it has no RHS, source-value, or satisfiability assumption.

`existsUnique_rhsFunctional` assumes:

- every row support has cardinality three;
- `U` satisfies `GoodQuestion row U`.

The cardinality premise supplies nonemptiness, while the first conjunct of `GoodQuestion` supplies pairwise disjointness. The proof lifts the independent incidence vectors to the subtype `equationSpan row U`, shows that they span that subtype, forms a basis, and uses `Module.Basis.constr` to assign `rhs e` to each basis vector. Basis extensionality proves uniqueness on the equation span. Because the selected equation vectors are independent, arbitrary RHS values are permitted; there is no hidden RHS-consistency premise.

The uniqueness is only uniqueness of a linear map on `equationSpan row U`. It does not assert a unique extension to `coordinateSpace row U` or to the ambient function space. Such extensions generally have free coordinates, so later work must retain the correct nonuniqueness boundary.

`actual_existsUnique_rhsFunctional` substitutes the actual occurrence-allocation support and RHS functions and discharges the global cardinality-three premise with `I.support_card`. It still explicitly requires `GoodQuestion I.support U`. This is a genuine wrapper over the actual source representation, but it says nothing about how `U` is sampled or how often it is good.

`equationSpan_finrank_eq_card` proves the expected dimension identity using the same independent family. It is consistent with the construction and useful for later counting or extension arguments, although the already-certified overlap-agreement theorem does not itself require the numerical finrank equality.

The Checks module exercises the actual wrapper on a nonempty one-row instance with RHS `1` and on the empty question. Those are suitable interface fixtures. They do not test a multirow nonempty question, but the general theorem and its coefficient-isolation proof cover arbitrary finite `U`; this is a review note rather than a blocking gap.

## Manuscript dependency discharged

The manuscript's star contract requires labels to respect the equation RHS values on the side-condition space `H_U`, and later transport must preserve that condition. The certified side-condition agreement theorem previously accepted an equation-span functional `g` together with a premise saying that `g` has the stored RHS on every selected equation vector. The present actual wrapper now constructs exactly such a `g` for every actual good question.

The valid dependency graph is therefore:

```text
actual support cardinality + GoodQuestion(U)
  -> independent selected equation vectors                         [closed here]
  -> unique RHS functional on equationSpan(U)                      [closed here]
  -> instantiate g in certified side-condition overlap agreement  [next composition]
  -> extend to coordinate/leaf spaces and glue on intersections    [open]
  -> minimal label transport and descent                           [open]
  -> actual star carrier, acceptance, and stationarity             [open]
  -> soundness/formula compilation/reduction assembly              [open]
  -> fixed-L headline hardness and learning corollary               [open]
```

The manuscript describes unique side-condition-preserving label transport as part of imported star machinery. This increment proves a necessary local functional construction but does not by itself replace that imported contract.

## Complexity boundary and remaining force-bearing gaps

1. **No efficient construction.** The module is in a `noncomputable section` and uses basis construction and classical choice. It proves mathematical existence and uniqueness on a finite vector space. It does not give an encoded algorithm, an FP witness, a polynomial bound, or a circuit/Turing-machine implementation for computing the functional.

2. **No source satisfiability.** The functional exists for an arbitrary RHS assignment because a good question selects disjoint rows. This is local consistency of the selected independent equations. It does not produce one assignment satisfying the original overlapping source instance, establish its YES promise, or weaken the need for the source-error transport already tracked separately.

3. **Coordinate-space extension and gluing remain open.** A linear extension from the equation span to the relevant coordinate or leaf space must be constructed, and the previously certified agreement theorem must then be instantiated to glue compatible maps on sums. Existence of an extension does not make it unique outside the equation span.

4. **Label transport remains open.** The exact label type, equivalence relation, transport map, inverse/uniqueness properties in the intended category, representative independence, and descent to manuscript leaf objects are not defined or proved here.

5. **Actual-star acceptance remains open.** The actual center and leaf carriers, restrictions, resampled question blocks, honest labeling, and implication from satisfied participating equations to star acceptance remain to be formalized. The present theorem contains no acceptance predicate or probability law.

6. **Stationarity and completeness assembly remain open.** No clique-resampling kernel, equal-fibre/detailed-balance argument, stationary marginal, rejection sampler, sampler runtime, or union over the original and resampled blocks is supplied. The previously proved one-block source-failure estimate cannot be transferred to every resampled block until these facts are available.

7. **Soundness and headline reduction remain open.** The smooth/advice outer game, modified star soundness and decoder, HN compilation, concrete CMMSA distribution, finite sampling/repair, encoded polynomial-time seeded map, promise preservation, coin and size bounds, source hardness instantiation, fixed-`L` asymptotics, and learning transfer remain outside this increment. Nothing here establishes NP-hardness, `P = NP`, `P != NP`, novelty, or publication readiness.

## Claim boundary and disposition

The defensible claim is:

> Lean verifies that the pairwise-disjoint three-coordinate equations in any actual good question have independent incidence vectors, so their stored right-hand sides define a unique linear functional on their equation span; that span has dimension equal to the number of selected equations.

Do not strengthen this to a unique coordinate-space or ambient extension, an efficient method for computing the functional, a satisfying assignment for the source instance, side-condition-preserving label transport, actual-star acceptance or stationarity, PCP soundness, a randomized reduction, the manuscript headline theorem, a P-versus-NP result, novelty, or publication readiness.

**GO-WITH-NOTES.** Accept the four frozen claims as the canonical completed RHS-functional construction obligation. The immediate next consumer should combine `actual_existsUnique_rhsFunctional` with the certified actual side-condition agreement theorem, while keeping coordinate-space extension, gluing, label transport, star acceptance/stationarity, and every hardness or efficiency claim explicitly open.
