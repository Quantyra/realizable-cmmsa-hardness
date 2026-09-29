# Initial-vertex and clique-resampling joint-law gap

## First missing force theorem

The committed `ActualOriginalPostPaddingVerifier.originalLawFromTagged` begins with a uniform eligible copied row set `U`, then a uniform transverse center `K`, ordered conditional leaves, and independent representatives of their full-vertex classes. It is a post-conditioning verifier law. It does not derive that law from a raw initial uniform full vertex followed by clique resampling.

To transfer **every arbitrary legal predraw table** from the raw verifier to `originalScore`, the next theorem needs a concrete raw joint finite law `μraw` on draws that expose the initial full vertex, all resampled full vertices (and their row sets `U'_i`), the center, and the ordered leaves. Let `GoodRaw` be legitimacy, let `μgood` be the normalized restriction of `μraw` to `GoodRaw`, and let `decode : GoodRaw → OriginalDraw` retain the verifier's actual sampled fields. The required statement is, for every source instance, copy count, and permitted `J,t,h,k`:

```
pushforward decode μgood = originalLawFromTagged I copies hcenter hleaf
```

For each legal center/leaf table pair `A` fixed before the draw, it also needs pointwise acceptance preservation on legitimate raw draws:

```
rawAccepts A ω ↔ originalAccepts I copies A (decode ω)
```

Those two statements imply equality of conditional fixed-table scores. If `a = μraw(GoodRawᶜ) < 1`, any raw failure event whose restriction is the decoded failure event has conditional failure at most raw failure divided by `1-a`. A bound on `a` alone does not establish the joint-law equality.

## Existing evidence and precise obstruction

- `ActualTaggedOrderedQuestionSourceBridge.orderedGood_pushforward` proves the uniform eligible `U` marginal from an **already legitimate ordered-row** law.
- `ActualTaggedVertexPhysicalLaw.uniform_independentChoice_pushforward` proves that already sampled independent presentation representatives push forward to uniform full-domain representatives in each queried class.
- `ActualTaggedVertexPresentationFiber.vertexPresentation_card` proves the same presentation count `2^(J·2h)` for every full vertex, and its `rows_eq_base` establishes that the row set is well defined by the vertex domain.
- `ActualTaggedQuestionRetainedMass` proves the raw ordered-row illegitimate mass `a`, the identity `goodMass = 1-a`, and, for its padding hypotheses, `1/goodMass ≤ 4/3 < 2`.

No formal raw initial-vertex/clique-resampling **joint** law, conditional pushforward to `OriginalDraw`, or raw legal-table acceptance map was found. The first additional counting fact for the manuscript's narrower `U'_i` marginal would be a constant-cardinality fiber `{v : TaggedPresentedVertex I copies J h // vertexRows v = U}` for every eligible `U`. The public domain-draw and presentation-fiber counts suggest this can be derived, but that marginal fact alone does not prove the joint score transfer.

The distinction is material: two resampled fair bits can be independent or perfectly correlated. Each bit is uniform in both laws, while the event that both equal one has probability `1/4` in the first law and `1/2` in the second. With multiple leaf checks and a fixed table, marginal uniformity alone cannot control their conjunction. `paper/body.tex:793` asserts each `U'_i` marginal is uniform and uses it for the honest-label **union-bound completeness** estimate in equation (21); it does not state the full joint pushforward needed for an arbitrary-table NO-soundness score identity.

This is an audit only; no new Lean theorem or assumption is introduced. The existing post-conditioning comparison still charges `2^-J` for class collisions. The raw initial-vertex to post-conditioning NO-soundness gap, including its exact `1/(1-a)` transfer, remains open until the raw joint kernel and the theorem above are specified and proved.
