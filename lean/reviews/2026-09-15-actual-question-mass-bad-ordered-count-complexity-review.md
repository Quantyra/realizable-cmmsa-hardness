# Bad ordered-question count: complexity-theory and manuscript review

Date: 2026-09-15  
Lens: top-level complexity theory / manuscript alignment  
Verdict: **GO-WITH-NOTES**

## Review scope and frozen artifacts

This was a read-only review of the frozen Lean source, its certification evidence, the current manuscript, and the planning ledger. I made no Lean edit, ran no compilation, and performed no commit, push, release, or public action.

- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean`: SHA256 `E87EE1F98ED5D431B288EB88AD278BE05D398461FAE4218A74A0CEDDBC792FC3`.
- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean`: SHA256 `E4A8CB6663501D7012E967D8B436366536B2AD0D49C6156C0A75882CBE52C36A`.
- Canonical evidence: `research/evidence/2026-09-15-actual-question-mass-bad-ordered-count-fresh-run/`.
- Evidence manifest `artifact-hashes.txt`: SHA256 `EB9B26EB3262E97D55B4E4E3BECAF0F01FF5EC46913E9B7152CA2F304C34C8FF`.
- Manuscript `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`: SHA256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`.
- Planning ledger `C:/Users/Dan/Desktop/Projects/IGH/Quantyra-Planning/docs/research/pvnp/full-theorem-obligation-ledger.md`: SHA256 `86D28592D0504911E681E687743518339BE35E0B7864F67CB9401166E292DFCC` at review time.

The evidence records main and Checks exit codes `0`, empty stderr, unchanged source hashes, and fresh target objects with hashes `D6FA76482E683528EEC2AF2F62B6F4E9CB7290CDA553669C6131BE36A09D460D` and `2676252E1CF77B93CB14B75088546A1EC3A930AD74552E02D9754C757B21282C`. The forbidden-token scan found no `sorry`, `admit`, or `native_decide`. The reviewed declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The run compiled the two frozen target modules against 2,794 recorded dependency objects seeded from the previous canonical run; it was not a rebuild of all dependencies from source. That disclosed provenance is sufficient for this increment.

## Statement and manuscript geometry

The new predicate is

```lean
def GoodOrderedQuestion
    {J : Nat} (row : E → Finset X) (u : Fin J → E) : Prop :=
  Function.Injective u ∧
    ActualStarQuestionSupport.GoodQuestion row (Finset.univ.image u)
```

This is the correct deterministic good event on the ordered sample space `Fin J → E`. Uniformly sampling that finite function space is exactly drawing `J` rows independently and uniformly with replacement. Injectivity removes repeated equation identities. `GoodQuestion` on the image then requires:

1. pairwise-disjoint supports of distinct selected rows; and
2. no global row `g` containing one coordinate from each of two distinct selected rows.

These are exactly the two geometric requirements in manuscript lines 171--180: `J` disjoint equations and no cross-equation pair of variables occurring together in any equation. The use of the image is safe because injectivity separately guarantees that it has exactly `J` elements. This predicate defines the event; it does not itself define a probability distribution, conditional sampler, or quotient to unordered questions.

## Bad-pair equivalence

The frozen theorem

```lean
theorem not_goodOrderedQuestion_iff_conflicting_pair
    (row : E → Finset X) (u : Fin J → E) :
    ¬ GoodOrderedQuestion row u ↔
      ∃ i j : Fin J, i ≠ j ∧ rowConflict row (u i) (u j)
```

matches the intended obstruction exactly.

- If `u` is noninjective, two distinct positions have equal row identities, activating the equality branch of `rowConflict`.
- If the selected image is not a `GoodQuestion`, failure of pairwise disjointness activates the direct-intersection branch, while failure of the no-cross clause supplies the global witness row and coordinates for the cross branch.
- Conversely, equality contradicts injectivity, direct overlap contradicts pairwise disjointness, and a cross witness contradicts the no-cross clause.

No row-linearity, source-value, probability, or hidden goodness premise is used. Although the cross relation is mathematically symmetric, the count only needs its displayed orientation.

## Counting argument

The generic result is

```lean
theorem bad_ordered_question_count_le
    (row : E → Finset X) (D J : Nat)
    (hthree : ∀ e, (row e).card = 3)
    (hdegree : ∀ x,
      ((Finset.univ : Finset E).filter
        (fun e => x ∈ row e)).card ≤ D) :
    ((Finset.univ : Finset (Fin J → E)).filter
      (fun u => ¬ GoodOrderedQuestion row u)).card ≤
      J * (J - 1) * (1 + 3 * D + 9 * D^2) *
        (Fintype.card E) ^ (J - 1)
```

The proof has the correct union-bound structure. For each ordered pair of distinct positions `(i,j)`, fixing the first row, choosing the second from a conflict neighbourhood of size at most `C`, and freely choosing the other positions gives at most

```text
C * |E|^(J-1)
```

tuples. There are exactly `J(J-1)` ordered position pairs. The bad-pair equivalence places every bad tuple in this union, and `conflict_degree_le` supplies `C = 1 + 3D + 9D²`. Duplicate witnesses only decrease the union cardinality. The separate `J < 2` branch correctly makes the bad set empty for `J = 0` and `J = 1`, so no positivity or lower-bound assumption on `J` was introduced.

This is a cardinality statement for the uniform ordered-row product law. If `|E| > 0`, dividing by the total `|E|^J` gives the intended bound

```text
Pr[bad] ≤ J(J-1)(1 + 3D + 9D²) / |E|.
```

That probability normalization, including denominator positivity and the corresponding retained-mass lower bound, is not yet in the frozen module.

## Actual-source consequence

For `I : ActualOccurrenceAllocation.Instance N m`, the already available declarations provide the exact premises with

```text
E   := I.RowId
X   := I.GlobalVar
row := I.support
D   := 4.
```

`I.support_card` gives three-uniformity, and `rowId_incidence_card_le_four I` gives the incidence premise on the same occurrence-indexed row universe. Hence the generic theorem mathematically entails

```text
# {u : Fin J → I.RowId | ¬ GoodOrderedQuestion I.support u}
  ≤ J(J-1) * 157 * |I.RowId|^(J-1),
```

because `1 + 3·4 + 9·4² = 157`. Repeated source owners remain separate row identities, as required by the occurrence construction. This exact actual-instance corollary is not exported in the frozen module, and the Checks module instantiates the generic theorem on `mixedRows` at `D = 3`, not on an `ActualOccurrenceAllocation.Instance`. The consequence is therefore justified by available compiled premises but remains an explicit Lean integration obligation.

## Distribution boundary and remaining bridges

The theorem supports the manuscript's raw independent uniform equation draws and the rejection of illegitimate tuples. It does not by itself establish the full law used later in the manuscript.

1. **Actual specialization.** Export the `D = 4`, `C = 157` corollary on `I.RowId`, then normalize it to a probability statement under the uniform function-space law.
2. **Disjoint-copy padding.** Define the copied row and coordinate universes and prove that supports from different copies are disjoint, the incidence bound remains four, the row count grows by the copy factor, and the YES/NO source value and degree promises are preserved. This is needed to make `157 J(J-1)/|I.RowId|` at most the manuscript's chosen `a`. The manuscript's `O(J²/N_outer)` notation also needs an explicit identification or comparison between `N_outer` and the copied row count.
3. **Retained mass and conditioning.** Prove `Pr[GoodOrderedQuestion] ≥ 1-a > 0`, construct or characterize the conditional law, and derive the factor `1/(1-a)` used at manuscript lines 1129--1132 and 1148--1155. The cardinality theorem alone does not produce an efficient rejection sampler.
4. **Ordered-to-subset law.** The manuscript subsequently treats `U` as a set/span object and says it is uniform over legitimate questions. Every legitimate `J`-element subset has exactly `J!` injective orderings, so conditioning the uniform ordered law and applying `u ↦ univ.image u` should induce the uniform law on legitimate subsets. That equal-fibre statement and the pushforward identity are not formalized here.
5. **Clique-resampling marginal.** Manuscript lines 1155--1158 additionally claim that each resampled `U'_i` is uniform over legitimate `U` because uniform resampling inside an equivalence class preserves the measure. This is a different distributional theorem and does not follow from the bad-tuple count or the ordered-to-subset equal-fibre fact.
6. **Weighted/nonuniform laws.** The present proof gives no bound for a nonuniform row distribution or a weighted tuple law. Such a use would require, for example, a maximum-atom bound or a weighted conflict-neighbourhood estimate. The manuscript's initial `U` law is explicitly uniform, so this is not a defect in the present theorem. It is a strict boundary: the later weighted star-projection CSP and occurrence weights cannot inherit this estimate without a separately proved distributional bridge.

After those steps, the larger unresolved path still includes the RHS functional and dimension theorem, minimal label transport, actual-star construction and acceptance, rational edge/formula tables, the FP and probability bridge, randomized-reduction assembly, learning corollary, and manuscript reconciliation.

## Decision

**GO-WITH-NOTES.** The frozen declarations correctly characterize bad ordered questions by a conflicting pair and prove the planned conservative count for the uniform ordered-row law, including the small-`J` cases. The result consumes the generic conflict-degree bound exactly as intended and yields the actual constant `157` once the existing actual-source premises are instantiated. It should be accepted as the completed generic bad-tuple obligation.

The accepted claim must remain narrow. This increment does not yet certify the actual `D = 4` corollary as a named theorem, the `O(J²/N_outer)` probability statement, copy padding, positive retained mass, conditioning loss, ordered-to-subset uniformity, clique-resampling marginals, any weighted/nonuniform analogue, actual-star acceptance, hardness, P versus NP, manuscript completion, or publication readiness.
