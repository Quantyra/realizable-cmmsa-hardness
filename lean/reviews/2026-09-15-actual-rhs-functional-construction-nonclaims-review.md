# Actual RHS-functional construction: non-claims-boundary review

2026-09-15. Top-level read-only review of commit `0ae4103373c1848a8ed6980cbca63784ab3a7025`, the frozen `ActualRhsFunctionalConstruction` main and Checks modules, and their target-fresh certification evidence. No Lean source, certification evidence, manuscript, release, push, or public claim was changed. This review file is the only artifact written by this lens.

## Verdict

**GO-WITH-NOTES.** The increment proves that equation vectors indexed by pairwise-disjoint nonempty rows are linearly independent; consequently, every supplied row-RHS assignment has a unique linear functional on the equation span of a good three-coordinate question. It specializes this statement to `ActualOccurrenceAllocation.Instance` and proves that the equation span has dimension equal to the number of selected rows.

This is the RHS-functional construction on the equation span only. It does not construct or uniquely characterize a functional on the coordinate space or any larger ambient space. It does not prove label gluing or transport, define a star carrier or acceptance predicate, establish clique stationarity, assemble the randomized reduction, establish source or target hardness, prove the manuscript headline theorem, or imply `P = NP` or `P != NP`.

## Frozen commit and evidence

The reviewed source commit is `0ae4103373c1848a8ed6980cbca63784ab3a7025` (`prove actual rhs functional construction`). The two tracked source files at that commit match the current frozen worktree files byte-for-byte.

| Artifact | SHA-256 | Review result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualRhsFunctionalConstruction.lean` | `A38112D36CED08F6D8AD151D85D08D1140CD8A17D40EFED8DEAB6B25E3100428` | Independently rehashed; matches both certification source snapshots. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualRhsFunctionalConstructionChecks.lean` | `59CD64CCACDE1E2F3BB286A600939187FD5C5DC93024BAB11DBB1F0E1A1DCB9B` | Independently rehashed; matches both certification source snapshots. |
| `research/evidence/2026-09-15-actual-rhs-functional-construction-fresh-run/artifact-hashes.txt` | `6DCE57B5372EEEEA857AC23C93662F5B6B64F7ABF520CCBE40BEC33C93163E3C` | Independently rehashed; matches `artifact-hashes-manifest.sha256`. All 36 rows were present and matched their recorded sizes and hashes. |
| `research/evidence/2026-09-15-actual-rhs-functional-construction-closeout.md` | `50FAE722706AF678BA7AEA26EBAFF38111FF7A83C899831D116C960CE398F5D2` | Wording and dependency boundary reviewed; no claim promotion found. |

The certification reports exit code `0` for `ActualStarQuestionSupport`, `ActualStarSpanIntersection`, `ActualFinite3LinSource`, the main module, and the Checks module. Their object hashes are respectively `8B4A75485327BA8836F8FDB1AB561ACD15DB816E8C7C16084C58DCEA0B9461FF`, `DECC2EAA887AC7C8C1DB4F121FC0B5A9BA03369FA191E1DE6B7CCA3FCE748DBD`, `72FE7300086DFB3B13844319C75725AC16032C3413699F20810B2282C6235F48`, `9A8526B28F205FD8153F9E43FB3A36DF374E6BADB4F7091C9C9721AFDA9D650F`, and `C46CFA10CD02A6F1E32B5B8F3B0AF359C413577D17633DD2BD1D05CB389636FF`.

The evidence describes a target-fresh sequential build under Lean `4.34.0-rc2` with `LEAN_NUM_THREADS=1`. The isolated target excluded the five named project-module artifacts and rebuilt them against an immutable seeded transitive dependency tree. The source-before and source-after inventories agree. This is strong evidence for the frozen increment within that dependency scope; it is not a from-source rebuild of Mathlib or the complete project graph.

The forbidden scan reports no `sorry`, `admit`, `native_decide`, `span_induction`, or explicit `axiom` declaration. `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound` for all four exported theorems. No project-specific axiom is reported.

## Exact proved boundary

`equationVectors_linearIndependent` assumes pairwise disjoint row supports on `U` and a nonempty support for each row in `U`. Its proof chooses a private coordinate from one row and evaluates a vanishing finite linear combination there. Pairwise disjointness makes all other summands zero, isolating the selected coefficient. The theorem is tied to the compiled `equationVector` incidence representation rather than an abstract substitute.

`existsUnique_rhsFunctional` assumes that every row has support cardinality three and that `U` is a `GoodQuestion`. Three-uniformity supplies nonemptiness; the good-question pairwise-disjointness supplies independence. The proof builds a basis of `equationSpan row U` from the selected equation vectors and uses `Module.Basis.constr` to assign each basis vector the supplied value `rhs e`. Basis extensionality proves uniqueness on that equation span.

The quantified uniqueness is therefore exact but domain-limited:

```text
existsUnique_rhsFunctional :
  exists! psi : equationSpan row U ->ₗ[ZMod 2] ZMod 2,
    forall e in U, psi (equationVector row e) = rhs e
```

It does not say that an extension to `coordinateSpace row U`, `L + H_U`, or an arbitrary ambient vector space is unique. Such extensions generally require additional data and need not be unique. The theorem also does not produce the coordinate-space map used by the previously certified side-condition agreement theorem.

`actual_existsUnique_rhsFunctional` supplies `row = I.support`, `rhs = I.rowRhs`, and the already compiled `I.support_card`. It remains conditional on a supplied good question `hU`. It does not construct an occurrence-allocation instance from an arbitrary hardness source, sample a good question, or prove a source-value or acceptance bound.

`equationSpan_finrank_eq_card` proves the manuscript-local dimension fact `dim H_U = J` when `J` is read as `U.card`, under the same three-uniform good-question assumptions. It is a finite linear-algebra fact, not the manuscript's star construction or transport contract.

## Fixtures

The one-row fixture is nonvacuous for the exported actual wrapper. `oneRowU` is a singleton, its row RHS is `1`, and `oneRowU_good` is proved. The instance's support-cardinality theorem used by the wrapper gives a three-coordinate support, so its equation vector is nonzero; satisfying RHS `1` therefore exercises a nonzero functional on a nonzero equation span. The fixture elaborates the exact existence-and-uniqueness conclusion rather than weakening it.

The separate empty-question fixture exercises the legitimate zero-dimensional branch. In that branch the row equations are vacuous and the zero-domain linear functional is unique. Keeping this case does not inflate the substantive one-row fixture or conceal a nonempty premise.

These are theorem-use and branch fixtures, not exhaustive semantic tests. They contain no coordinate-space extension, two-question overlap, transported label, star edge, sampler, or acceptance behavior.

## Manuscript dependency and remaining boundary

The manuscript's star-construction contract states both that `H_U` has dimension `J` and that leaf labels satisfy the equation right-hand sides on `H_U`; this increment supplies the corresponding local equation-span dimension and unique RHS functional. The same paragraph additionally asserts unique side-condition-preserving label transport, a star test, uniform representative resampling within equivalence classes, and value preservation. None of those later assertions is discharged here.

The immediate legitimate consumer is specialization of the already certified side-condition agreement theorem using the constructed equation-span map. A separate coordinate-space or ambient extension must be constructed and its generator equations proved before that agreement theorem can be instantiated on both sides. The remaining path is at least:

```text
construct the needed coordinate-space/ambient extension
  -> specialize side-condition agreement with both concrete maps
  -> define and prove minimal label gluing/transport
  -> construct the actual star carrier and acceptance theorem
  -> prove clique-resampling stationarity and value/failure transport
  -> connect source completeness and soundness
  -> implement and verify the polynomial-time randomized reduction
  -> discharge fixed-parameter quantitative consumers
  -> reconcile the learning corollary and manuscript headline theorem
```

## Claims that remain prohibited

The accepted description is: **Lean constructs the unique row-RHS functional on the equation span of a good actual three-coordinate question and proves that span has dimension equal to the question's row count.**

Do not describe this increment as a unique coordinate-space or ambient extension, label construction, label transport, star construction, star acceptance, clique stationarity, source-hardness instantiation, randomized reduction, NP-hardness proof, manuscript completion, novelty or publication certification, `P = NP`, or `P != NP`.

The closeout's current `PASS; review pending` wording and its explicit limitations are accurate for pre-review certification. With this lens, the increment is acceptable as one local dependency, subject to the other two required review lenses and the remaining construction and reduction obligations above.
