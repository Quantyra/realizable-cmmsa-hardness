# Actual finite 3-LIN semantic carrier: non-claims-boundary review

2026-09-15. Read-only review of the frozen `ActualFinite3LinSource` increment, its Checks module, the canonical seeded-dependency evidence, and the S3138 claim boundary. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment defines a finite 3-LIN semantic carrier and instantiates it from the actual occurrence allocation while preserving the indexed row entries, support, right-hand side, per-row badness predicate, total violation count, and row-ID cardinality. These are the exact semantic facts proved by the module.

The increment does not construct tagged copies or prove copied row count, copied degree, pair-intersection preservation, cross-copy disjointness, copied assignment transport, copied violation decomposition, optimum-value preservation, a polynomial producer, a global independently tagged tuple law, retained mass, conditioning, hardness, P versus NP, novelty, or publication readiness.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualFinite3LinSource.lean` | `3109F8B0078B7F6253110ED2C39FC85935268768AB0A0A6B9CDA2F029B8B761F` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualFinite3LinSourceChecks.lean` | `469AC0A70E0339B21706A7696E173C2C6E19CB211C6AAEF6135F0ECAE3AB8A0F` | Matches the routed freeze. |
| `research/evidence/2026-09-15-actual-finite-3lin-source-fresh-run/manifest.txt` | `00C7B7E93ED9BEFD2F0B351E6E9E9C04455D7A576D5C37D3211D0F7161DAAE9C` | Matches the routed evidence-manifest hash. |

The evidence records main and Checks exit codes `0`, empty stderr, emitted object hashes `72FE7300086DFB3B13844319C75725AC16032C3413699F20810B2282C6235F48` and `69793BC0944858BF5846E32D23956F29A20D852AA3C18FF30FDBE1E9D7D4E008`, and a clean forbidden-token scan. The Checks transcript reports only `[propext, Classical.choice, Quot.sound]` for the reviewed declarations.

The target was populated by recursively copying an immutable prior canonical dependency object tree. The current main and Checks objects were absent before compilation and were emitted sequentially. This is fresh compilation of the two frozen targets against recorded cached dependencies, not a fresh rebuild or independent revalidation of all transitive dependencies. Claims about certification must preserve that caveat.

## Exact semantic boundary

The carrier contains only:

```lean
structure Finite3LinSource
    (Row Var : Type*) [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var] where
  row : Row → Fin 3 → Var
  rhs : Row → ZMod 2
  row_injective : ∀ q, Function.Injective (row q)
```

Its derived `support`, `badRow`, and `violations` definitions describe a finite three-variable linear-equation source over `ZMod 2`. The generic helper `row_injective_of_support_card` shows coordinate injectivity from the exact image-support representation and support cardinality three.

For an actual occurrence allocation `I`, `Finite3LinSource.ofActual I` uses `I.RowId` and `I.GlobalVar` directly. The reviewed interface proves:

- `ofActual_row`: each coordinate is definitionally the actual indexed row coordinate;
- `ofActual_support`: the carrier support equals `I.support q`;
- `ofActual_rhs`: the carrier right-hand side is definitionally `I.rowRhs q`;
- `ofActual_badRow`: carrier badness equals actual badness on the pair `(I.row q, I.rowRhs q)`;
- `ofActual_violations`: the sum over `RowId` equals `I.violations x`;
- `rowId_card_eq_rows_length`: `Fintype.card I.RowId = I.rows.length`.

The row-count theorem is an identity between the indexed row-ID universe and the length of the existing actual row list. It does not multiply rows, construct a new universe, or establish an outer-equation count beyond that existing representation.

`ofActual_violations` is assignmentwise equality for a fixed assignment `x : I.GlobalVar → ZMod 2`. Quantifying this equality over assignments may later support an optimum-value bridge, but no optimum, minimum, satisfaction fraction, or assignment restriction/extension theorem is defined or proved here. It must not be reported as source-value preservation for a copied source.

## Fixture audit

The Checks fixture uses `violatedSource : Instance 1 1`, the original row ID `Sum.inl 0`, and the zero assignment against right-hand side one. It verifies the row-count signature, exact support transport, RHS transport, an actually violated original row, bad-row correspondence, and total-violation correspondence.

This is a useful semantic transport fixture. It does not exercise an internal equality row, a satisfying assignment, multiple-row aggregation, numeric evaluation of the total violation count, any tag, any copy, assignment restriction or extension, or any optimum-value statement. Those omissions are consistent with this carrier-only increment and provide no evidence for the later S3138 obligations.

## S3138 boundary

S3138 correctly labels the interface as a conditional route through a semantic carrier and rejects raw-instance replication because it changes occurrence/cloud semantics. This increment discharges the prerequisite semantic-carrier interface only. S3138 remains **Active**, and its stop-loss remains controlling: carrier and cardinality lemmas alone cannot close the story or justify proceeding to conditioning, star acceptance, or paper claims.

The remaining S3138 obligations include:

- explicit tagged copied row IDs and variables;
- row-count multiplication, support cardinality three, degree at most four, pair-intersection preservation, and cross-copy disjointness;
- copied RHS and satisfaction transport under assignment restriction and extension;
- violation decomposition and exact optimum violation/satisfaction fraction preservation for positive copy count;
- an encoded polynomial-time/output-size producer;
- the global uniform independently tagged ordered-row law and its projection;
- identification with the manuscript outer equation universe;
- a copy-count choice that yields the required positive retained mass.

In particular, the present row/support/RHS/badness/violation equalities concern `ofActual I` on the unchanged types `I.RowId` and `I.GlobalVar`. They do not imply any of these copied-source conclusions.

## Direct consumer and required wording

The direct consumer is the tagged-copy definition built over `Finite3LinSource`, followed first by structural copy lemmas and assignmentwise violation decomposition. An exact optimum-value theorem then needs both assignment projection and extension directions, plus a positive copy count where division by the copied row count is used.

The strongest justified description is:

> Lean now packages the actual occurrence allocation as a finite 3-LIN semantic source and proves exact preservation of its indexed rows, supports, right-hand sides, row badness, assignmentwise total violation count, and row count. Tagged copying and source-value preservation remain open.

Do not describe this increment as a copied construction, source-preserving padding, value preservation, a producer, a tuple-law theorem, retained-mass control, a completed actual-source bridge, a randomized reduction, hardness, a P-versus-NP result, a novelty result, or a publication-ready result.

## Material findings

1. The theorem surface proves exactly the intended carrier and unchanged-source semantic transport facts.
2. Row identities are preserved through `I.RowId`; `rowId_card_eq_rows_length` does not collapse equal row values.
3. Assignmentwise violation equality is narrower than optimum-value preservation and supplies no copied-source result by itself.
4. The fixture meaningfully checks a violated original row but supplies no evidence about tags, copies, assignment transport, or value.
5. The receipt certifies the frozen main and Checks against documented seeded dependencies, not a full transitive rebuild.
6. S3138 remains open under its stated stop-loss, and no public-claim promotion follows from this review.
