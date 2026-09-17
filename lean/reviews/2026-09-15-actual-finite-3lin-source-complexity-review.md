# Actual finite 3-Lin source complexity/manuscript review

## Verdict

**GO-WITH-NOTES** for this frozen interface increment. The carrier and `ofActual` bridge are mathematically faithful to the post-regularization semantic row system and are suitable inputs to the tagged-copy value proof. They do **not** yet prove copy padding, optimum-fraction preservation, a polynomial producer, or the manuscript's global independently sampled law. S3138 therefore remains active.

## Reviewed artifacts

- Main: `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualFinite3LinSource.lean`
  - reviewed SHA-256: `3109F8B0078B7F6253110ED2C39FC85935268768AB0A0A6B9CDA2F029B8B761F`
- Checks: `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualFinite3LinSourceChecks.lean`
  - reviewed SHA-256: `469AC0A70E0339B21706A7696E173C2C6E19CB211C6AAEF6135F0ECAE3AB8A0F`
- Fresh evidence: `research/evidence/2026-09-15-actual-finite-3lin-source-fresh-run/`
  - manifest SHA-256: `00C7B7E93ED9BEFD2F0B351E6E9E9C04455D7A576D5C37D3211D0F7161DAAE9C`
  - recorded main/checks exits: `0/0`
  - recorded main/checks object SHA-256: `72FE7300086DFB3B13844319C75725AC16032C3413699F20810B2282C6235F48` / `69793BC0944858BF5846E32D23956F29A20D852AA3C18FF30FDBE1E9D7D4E008`
  - forbidden-token scan: clean
  - reported axioms: `propext`, `Classical.choice`, `Quot.sound`
- Planning contract: `stories/S3138-source-preserving-tagged-copy-padding.md`
- Interface audit: `docs/research/pvnp/s3138-tagged-copy-interface-risk-audit-2026-09-15.md`
- Literature note: `docs/research/pvnp/literature-review-source-preserving-copy-padding-2026-09-15.md`
- Manuscript: `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`
  - reviewed SHA-256: `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`
  - relevant passages: outer-game contract at lines 158--170 and padding/conditioning claims at lines 1148--1175

This was a read-only mathematical/manuscript review. I did not compile or change Lean sources.

## Semantic bridge assessment

`Finite3LinSource` carries exactly the data needed to regard the emitted object as a finite 3-Lin system: a finite row type, a finite variable type, three distinct variables per row, and one GF(2) right-hand side per row. Its `badRow` and `violations` definitions use the same three-term equation and count one unit for each bad row identity.

The bridge is exact at the current semantic level:

| Required correspondence | Frozen theorem | Assessment |
|---|---|---|
| Row positions | `Finite3LinSource.ofActual_row` | Exact definitional equality |
| Three-variable support | `Finite3LinSource.ofActual_support` | Exact equality with `I.support` |
| Right-hand side | `Finite3LinSource.ofActual_rhs` | Exact definitional equality |
| Per-row violation | `Finite3LinSource.ofActual_badRow` | Exact definitional equality with the indexed actual row/RHS pair |
| Total violations | `Finite3LinSource.ofActual_violations` | Exact equality for every assignment, via `I.violations_eq_index_sum` |
| Row multiplicity/identity | `Instance.rowId_card_eq_rows_length` | Exact cardinality equality; it counts `RowId` identities and matches the emitted list length |

The total-violation theorem is the material bridge. Because both sides range over the same assignment type `I.GlobalVar -> ZMod 2`, it is strong enough to derive equality of any subsequently defined minimum violation count and violation fraction for `ofActual I`. No source promise or approximation is introduced by this conversion.

That consequence is not yet present as a Lean theorem. `Finite3LinSource` currently has no optimum, minimum-violation, satisfaction-fraction, or value definition. Therefore the current increment supports the value-preservation route but does not itself discharge S3138's exact optimum-fraction obligation.

## `RowId` and `N_outer`

`rowId_card_eq_rows_length` proves

```text
Fintype.card I.RowId = I.rows.length.
```

This resolves the internal denominator mismatch between uniform sampling from `I.RowId` and counting the emitted post-regularization row list. It does not prove that this quantity equals the raw source equation count `m`; in fact the existing count theorem gives `I.rows.length = m + 4 * I.edgeCount`.

The manuscript currently introduces `N_outer` as the size of the outer equation universe and later uses it in the `O(J^2/N_outer)` exclusion estimate. The formal route can make that statement correct by defining the post-regularization semantic system `ofActual I` to be the outer instance supplied to the repeated game and setting

```text
N_outer := Fintype.card I.RowId = I.rows.length.
```

That interpretation still needs an explicit manuscript/formal interface theorem connecting the encoded upstream reduction, its YES/NO fraction guarantees, and this emitted system. `rowId_card_eq_rows_length` alone does not identify the manuscript notation, does not transport the upstream hardness promise, and does not construct the game's sampling law.

## Remaining exact dependency path

The next integrated formal increment should stay on the value path rather than close on more carrier packaging:

1. Define tagged copies with rows `Fin K x Row`, variables `Fin K x Var`, row map `(k,q,i) |-> (k,I.row q i)`, and copied RHS `I.rhs q`.
2. Prove restriction and repeated-assignment laws, including exact copied `badRow` equivalence.
3. Prove the violation decomposition

   ```text
   copied.violations x = sum k, I.violations (fun v => x (k,v)).
   ```

   and repeated-assignment multiplication by `K`.
4. Define the base and copied minimum violation counts or equivalent optimum fractions. For `K > 0` and positive base row cardinality, prove both inequalities and exact fraction equality. The lower direction applies base optimality separately to every tag; the upper direction repeats a minimizing base assignment.
5. Transport the actual YES/NO fraction statements to `ofActual I` and then to its copies. The exact `ofActual_violations` theorem handles the semantic conversion, while `ActualRegularization` supplies only conditional YES/NO guarantees from explicit source promises. It does not supply the upstream hardness producer.
6. Prove cardinality multiplication, support size three, degree at most four, same-tag conflict preservation, and cross-tag disjointness, then instantiate the existing good-mass theorem with copied row cardinality `K * Fintype.card I.RowId`.
7. Prove the global product-law equivalence for uniform independent samples in `Fin J -> (Fin K x Row)`. The tag and base-row projections must be independently uniform. A one-tag mixture law would leave all `J` rows in one component and would not dilute bad-tuple mass.
8. Select an explicit positive `K` from the fixed manuscript parameters so that the bad mass is at most `min(tau/100, 1/4)`, and prove positive retained mass before conditioning.
9. Define the encoded `tagCopiesFn`, prove decode correctness and membership in the repository's FP model, and give its output-size bound. The current noncomputable type-level carrier provides no algorithmic evidence. If `K` is fixed after the manuscript parameters, linear expansion in `K` is polynomial; if it is computed from the source size, that computation and bound must be formalized.
10. Connect the independently sampled copied-row law to the star construction, legitimate conditioning, clique-resampled marginals, and the final randomized-reduction assembly.

## Complexity and manuscript boundaries

The bridge does not worsen or weaken the actual violation semantics. It also does not establish exact equality between the raw source optimum and the regularized optimum. The available regularization results instead give exact completeness-side extension counts and a scaled soundness-side lower bound under explicit source hypotheses. The paper must state that distinction when the post-regularization system becomes the outer game instance.

The carrier is noncomputable and parameterized by arbitrary finite types. `ofActual` is a semantic coercion, not an encoded transformation. No runtime, output-size, uniformity, or FP result follows from it.

The manuscript's assertion that copies preserve value and degree is still unproved in Lean. The current theorem preserves actual violations only before copying. Likewise, no global `J`-row law, retained-law marginal, conditioning estimate, star acceptance theorem, outer hardness instantiation, randomized reduction, P-versus-NP implication, or publication claim follows from this increment.

## Packaging-drift check

No material packaging drift is present in the frozen increment. The carrier removes a real representation ambiguity and `ofActual_violations` is immediately consumable by the tagged-copy optimum proof. The route becomes packaging drift if subsequent work accumulates support/cardinality conveniences without landing violation decomposition, both directions of optimum-fraction preservation, the global product law, and the encoded producer required by S3138's stop-loss.

## Acceptance conditions for the next review

The next S3138 review should reject closure if any of the following occurs:

- copied value is asserted from repeated assignments alone, proving only one inequality;
- row copies are tagged but variables are shared across tags;
- `N_outer` is silently identified with raw `m` rather than the sampled semantic row cardinality;
- the verifier samples one common copy tag for all `J` rows;
- a noncomputable `Fintype` construction is described as an FP producer;
- source hardness or exact raw-to-regularized optimum equality is inferred from the current conditional regularization lemmas;
- conditioning or star acceptance is claimed before positive retained mass and the correct global law are formalized.
