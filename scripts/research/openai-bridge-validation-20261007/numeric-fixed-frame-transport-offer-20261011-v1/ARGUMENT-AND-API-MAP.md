# Argument and API map: fixed-frame star transport

This offer establishes the direct transport needed to run the ordinary star experiment in one fixed coordinate frame. The public statements are `starAccepts_coordinate_iff` and `starDensity_coordinate_eq` in `ActualCoordinateStarDensity.lean`.

`starAccepts_coordinate_iff` quantifies over arbitrary center and leaf tables. For each center vector `x`, the proof maps it through the induced equivalence from the original center subspace to its coordinate image. Both the center label and each leaf label are precomposed with inverse induced equivalences. Since the leaf contains the center, the two restriction paths evaluate at the same original `x`; equality is therefore equivalent in both directions. The proof handles every `i : Fin k` separately and assumes neither disjoint leaves nor a common ambient functional. Repeated and overlapping leaf labels remain unrestricted.

`starDensity_coordinate_eq` reindexes the finite outer center sum by `grassCoordinateEquiv`, then the ordered `Fin k`-indexed leaf tuple sum by the pointwise `extensionCoordinateEquiv`. Those equivalences preserve the nested experiment: uniform center, followed by `k` independent uniform containing leaves. Their carrier cardinalities agree, and the full acceptance indicator agrees by the first theorem. The resulting equality is the exact `StarDensity` value on the fixed complement and on `CoordAmbient J`, with the same `t,d,k` and arbitrary tables.

The fixed frame is the `actualCoordinateEquiv` attached to the already selected `SideComplement`; neither theorem chooses a new complement or changes the frame by table or leaf index. The imports and their transitive definitions are pinned below. `ActualMaximalPairLadder` supplies the decoded-pair and codimension definitions.

## Exact remaining decoded-pair obligation

The source defines `pullbackDecodedPair` with `Qpull = (grassCoordinateEquiv A).symm Q`, `Wpull = P.W.map (actualCoordinateEquiv A).symm.toLinearMap`, and the functional pulled back through the induced equivalence `P.W ≃ Wpull`. Its constructor proves `Qpull.val ≤ Wpull`; `pullbackDecodedPair_finrank` and `pullbackDecodedPair_codim` preserve the decoded dimension and exact codimension, hence any `q + codim W = r` budget.

`pullbackZoomEquiv` maps every intermediate `d`-space through that same fixed Grassmann equivalence and carries both bounds in the zoom definition. `pullbackAgreesOn_iff` is the required evaluation square: the table and decoded functional are transported through their induced domain equivalences. It restricts the zoom equivalence to `pullbackAgreeingZoomEquiv`, giving exact equality of both zoom cardinalities. `pullbackAgreement_eq` rewrites the full rational agreement definition through those cardinalities, including its empty branch; `pullbackAgreement_real_eq` applies the Real cast. No common functional over the ambient space or `jointlyDirect` premise is introduced.

Status: complete source offer, uncompiled. The exact acceptance boundary is syntax, typeclass, and kernel verification of these declarations and their pinned dependencies on GCP; no mathematical or certification acceptance is claimed. If the transport proof fails, the first exact repair targets are the subspace-map equalities in `pullbackZoomEquiv` and the evaluation simplification in `pullbackAgreesOn_iff`.
## Step-to-claim crosswalk

| Declaration or record | Exact argument step |
| --- | --- |
| `starAccepts_coordinate_iff` | Restriction naturality on the fixed center, for every leaf occurrence; full pointwise acceptance iff |
| `starDensity_coordinate_eq` | Reindex center and independent ordered-leaf sums; preserve uniform masses and the full-event indicator |
| `pullbackDecodedPair`, `pullbackDecodedPair_finrank`, `pullbackDecodedPair_codim` | Pull back the decoded subspace and functional through the same fixed frame; preserve subspace dimension and codimension |
| This map | Zoom/agreeing-zoom equivalence, rational and Real agreement remain unformalized |

Status: uncompiled source offer. The inherited v1 directory was inspected read-only and remains untouched. No Lean, Lake, GCP, or Git command was run.