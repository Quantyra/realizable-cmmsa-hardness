# Proof-adversarial review: actual finite 3-LIN source bridge

**Verdict: GO-WITH-NOTES.** The frozen increment defines a faithful finite, indexed three-variable linear-equation source and constructs it from the actual occurrence allocation without losing row identity, support, RHS orientation, or violation multiplicity. The cardinality and injectivity arguments are sound. The notes are downstream obligations: the copied-source violation identity is still a consumer to be proved, the structure is a semantic finite object rather than an encoded polynomial-time producer, and the fixture establishes a genuinely violated row but does not normalize the total violation count to a numeral.

## Frozen artifacts and evidence

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualFinite3LinSource.lean` | `3109F8B0078B7F6253110ED2C39FC85935268768AB0A0A6B9CDA2F029B8B761F` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualFinite3LinSourceChecks.lean` | `469AC0A70E0339B21706A7696E173C2C6E19CB211C6AAEF6135F0ECAE3AB8A0F` |
| canonical `manifest.txt` | `00C7B7E93ED9BEFD2F0B351E6E9E9C04455D7A576D5C37D3211D0F7161DAAE9C` |

The evidence directory is `research/evidence/2026-09-15-actual-finite-3lin-source-fresh-run/`. I independently recomputed the three routed hashes above and every entry recorded in `manifest.txt`; all match. Main and Checks exited `0` with empty stderr. The resulting objects have SHA-256 values `72FE7300086DFB3B13844319C75725AC16032C3413699F20810B2282C6235F48` and `69793BC0944858BF5846E32D23956F29A20D852AA3C18FF30FDBE1E9D7D4E008`. Both current objects were absent before compilation. The target used an immutable dependency-object seed from the prior canonical `actual-question-mass-d4-count` target, so this is a target-fresh main-and-Checks certification against pinned dependencies rather than a source rebuild of every dependency.

The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and user-declared axioms. Checks reports only `propext`, `Classical.choice`, and `Quot.sound` for every reviewed declaration.

## Structure and row-local injectivity

`Finite3LinSource Row Var` stores

```lean
row : Row → Fin 3 → Var
rhs : Row → ZMod 2
row_injective : ∀ q, Function.Injective (row q)
```

and derives the support as `Finset.univ.image (row q)`. Thus a `Row` remains an indexed equation occurrence; rows having equal mathematical content are not quotient-identified. `violations` sums over the entire finite row type, so its semantics count row identities with multiplicity.

`row_injective_of_support_card` is valid. After rewriting the supplied support to the image of `Fin 3`, the hypotheses give

```text
card (image (row q) univ) = card (univ : Finset (Fin 3)).
```

`Finset.card_image_iff` then gives injectivity on `univ`, which is global injectivity because both indices are members of `univ`. The proof does not infer injectivity merely from an unconnected support-cardinality assertion: `hsupport` explicitly identifies that support with the row image. For `ofActual`, the two premises are supplied by the already proved `I.support_eq` and `I.support_card`, covering original and gadget rows.

The structure's `Fintype` and `DecidableEq` parameters make it convenient for finite sums and supports but make the semantic object depend on chosen typeclass instances. `ofActual` uses a local `Classical.decEq` for `RowId`; this is logically harmless and reflected by `Classical.choice` in the axiom profile. A later encoded reduction should not cite this noncomputable construction as an implementation or runtime result. It must separately provide computable row/variable encodings and enumeration costs.

## Row-count identity

`rowId_card_eq_rows_length` preserves occurrence identity. It rewrites `I.rows` as the map of `I.rowIndices`, removes only the length-preserving map, and computes the length of `rowIndices` from its `Nodup` exhaustive `toFinset = univ` representation. It does not convert the list of row/RHS values to a set and does not require injectivity of the row/RHS map. Therefore the equality remains valid at the intended list-multiplicity level even if two semantic equations were ever equal.

## `ofActual` correspondence and equation orientation

The construction takes `row := I.row` and `rhs := I.rowRhs` definitionally. The exported correspondences have the required strength:

- `ofActual_row` is pointwise definitional equality for every row identity and each ordered position in `Fin 3`;
- `ofActual_support` rewrites the derived image support to the actual support using `I.support_eq` in the correct orientation;
- `ofActual_rhs` is definitional equality and preserves original RHS values and equality-cloud RHS values;
- `ofActual_badRow` is definitional equality to `I.badRow x (I.row q, I.rowRhs q)`;
- `ofActual_violations` rewrites the list-count implementation with `I.violations_eq_index_sum` and then closes definitionally.

Both `badRow` definitions test exactly

```text
¬ (x(row q 0) + x(row q 1) + x(row q 2) = rhs q).
```

There is no reversal of satisfied and violated equations, no negation mismatch, no reordering of the three summands, and no change from Boolean equality to an inequivalent arithmetic predicate. Over `ZMod 2`, ordering would be extensionally harmless, but the bridge is stronger: the expressions are definitionally identical. The final equality also counts over `RowId`, while `violations_eq_index_sum` proves that this indexed sum equals the original ordered-list `countP`; row occurrences are neither deduplicated nor silently reindexed.

## Fixture nonvacuity

The Checks fixture has one original equation whose three source owners repeat but whose occurrence anchors are distinct, and whose RHS is `1`. Under the zero assignment, Checks proves the actual row predicate is `true`. It also instantiates support, RHS, bad-row, total-violation, and row-count correspondence theorems. Consequently this is not an empty-source or satisfied-row-only fixture, and it exercises the repeated-owner case that motivated occurrence allocation.

The fixture does not directly state

```lean
(Finite3LinSource.ofActual violatedSource).badRow zeroAssignment originalId = true
```

or normalize either total violation count to a numeral. The proved actual `true` fact and `ofActual_badRow` imply the displayed target fact immediately, so this is a presentation and regression-strength note rather than a gap in the generic proof. A later copied-source Checks file should include an explicit positive copied violation and a nonconstant assignment across two copies.

## Direct copied-violation consumer

The immediate consumer should be a disjoint-copy construction with row type `Fin K × Row`, variable type `Fin K × Var`,

```lean
copied.row (c, q) i := (c, I.row q i)
copied.rhs (c, q) := I.rhs q
```

and the exact decomposition

```lean
copied.violations x =
  ∑ c : Fin K, I.violations (fun v => x (c, v)).
```

For a replicated assignment it should derive

```lean
copied.violations (fun cv => a cv.2) = K * I.violations a.
```

The actual-source specialization must consume `Finite3LinSource.ofActual_violations` directly, so that copying the semantic source is connected back to `ActualOccurrenceAllocation.Instance.violations` rather than to a newly introduced, assumed value. Together with `Fintype.card (Fin K × Row) = K * Fintype.card Row`, the arbitrary-assignment decomposition supplies both directions needed for exact preservation of optimum violation fraction: replicate a base assignment for one direction, and apply the base lower bound separately to each copy restriction for the other. The copied construction must also prove support disjointness across copy tags and preserve the local incidence bound.

These consumer theorems are not present in the frozen increment. Accordingly, this review accepts the source bridge but does not certify copy padding, value preservation, retained-mass positivity, conditioning, the full source instantiation, the randomized reduction, hardness, or a P-versus-NP conclusion.

## Disposition

**GO-WITH-NOTES.** The kernel-checked bridge faithfully preserves the actual finite 3-LIN row system and its violations, and its proof handles the dangerous identity and orientation issues correctly. Before the source route advances, freeze and prove the copied-violation decomposition above, its actual-source specialization through `ofActual_violations`, and the row-count/value consequences. Keep computational encodings and polynomial runtime as separate explicit obligations.
