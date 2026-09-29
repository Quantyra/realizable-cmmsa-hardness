# Encoded outer YES to copied occurrence Eq21

`ActualOuterEncodedOccurrenceYesBridge.lean` connects the visibly external
`ExternalMZOuterSource` YES output to the concrete copied-row assignment
premise consumed by the declared common-draw Equation (21) proof. The
external MZ structure has **no constructed inhabitant**; its encoded SAT
reduction, fixed parser, and source game law/value remain external contracts.

For each encoded 3Lin output `E`, `occurrenceOfEncoded E` uses its actual
`Fin E.rows` row map and right-hand sides. The source count is preserved
exactly. `sourceExtension` across occurrence equality clouds preserves that
count, and repeating it on any number of disjoint copies induces one ambient
F₂ linear functional. Lean proves its copied `badRows` count equals copies
times the source violation count. Since the actual generated occurrence
instance has at least `E.rows` total rows, `NearSatisfiable E ε` with `ε≥0`
implies the precise `PositiveErrorAssignment` used in the common-draw proof.
This argument does not assume exact satisfiability.

The `s<1` and `κ>0` constants live in the external MZ structure before the
later error. `exists_late_outer_error` chooses `0<ε<1-s` with
`ε≤τ/[100(blocks+1)J]` after fixed `blocks,J` and arbitrary `τ>0`.
`external_yes_exists_padded_assignment` takes an actual encoded SAT YES
output and then selects `T≥4` after `τ`, with
`copies=actualPaddingCopies J T`. It proves the actual raw collision mass
`a≤τ/100` and `a≤1/4`, actual tagged good mass `1-a`, and existence of
the concrete copied ambient `f` satisfying `PositiveErrorAssignment`.
The earlier raw-law bridge identifies raw legitimacy mass with `1-a` under
the positive copy and source-row hypotheses.

`parsed_outer_yes_common_draw` consumes that source YES output at a fixed
parsed `E`, a fixed copy count, and the **explicit** nonempty raw, eligible,
presented, center, and leaf fibres. Under `t≤2h`, `h≤J`, positive copy and
row counts, `ε≤τ/[100(blocks+1)J]`, and `a≤1/4`, it applies
`ActualCommonBlockYesComposition.common_draw_yes_failure_le`: the one fixed
honest table's declared `OriginalDraw` rejection probability is at most
`τ/75`. The theorem does not equate the conditioned-draw probability times
raw legitimacy mass with a common raw joint event.

The module target built green (3490 jobs), and its Checks target built green
(3491 jobs). Axiom prints for the main bridges show only `propext`,
`Classical.choice`, and `Quot.sound`; this does not prove the external MZ
fields.

**Remaining conditional dependencies:** no Lean inhabitant of
`ExternalMZOuterSource`; fixed encoding/parser computational implementation;
nonempty geometric fibres at the selected encoded instance and padding;
fixed-parameter encoded runtime for occurrence allocation, copy padding,
sampler, and final reduction; and the full NO-soundness path. The result
reduces the YES assignment and late-padding gap, but does not complete core
Theorem 1 or change the NO gap.

## Three-lens bounded review

| Lens | Verdict | Boundary |
| --- | --- | --- |
| Proof adversarial | **GO-WITH-NOTES** | The encoded YES assignment maps to the actual occurrence and copied `PositiveErrorAssignment` with exact violation counts. Late `ε`, padded `T`, and conditional `τ/75` are separately composable; no single theorem yet carries the chosen `ε,E,T` and required geometric fibres through the entire chain. |
| Complexity theory | **GO-WITH-NOTES** | The external MZ encoded reduction is still an uninhabited contract. The actual occurrence and copy operations have no proved encoded fixed-parameter runtime. The selected-padded instance's geometric fibre nonemptiness is a separate obligation. |
| Non-claims boundary | **GO-WITH-NOTES** | The `τ/75` result is for the declared conditioned draw under explicit fibre hypotheses. The scalar probability product is not a common raw joint-event identity. Core Theorem 1 remains **INCOMPLETE**, and the NO-soundness gap is unchanged. |

This review closes only the bounded source-to-copied YES bridge.
