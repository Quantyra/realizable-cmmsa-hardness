# Tagged vertex representative law: GCP Lean receipt

- Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`.
- Isolated checkout: `/tmp/tagged-vertex-presentation-fiber-r1`.
- Exact-source command: `lake build PvNP.RealizableHardness.ActualTaggedVertexPhysicalLawChecks`.
- Terminal run: `/tmp/tagged-vertex-physical-law-checks-r12.log`, PID 17111, exit 0, `Build completed successfully (3237 jobs)`. This exact log is copied as `checks.log`.
- `#print axioms` on `vertexPresentation_card`, `uniform_classRepresentative_pushforward`, `taggedPhysicalAccepts_vertex_invariant`, `uniform_independentChoice_pushforward`, and `taggedPhysicalMean_eq_vertexMean` returned only `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA256:

| Lean module | SHA256 |
| --- | --- |
| `ActualTaggedPresentationFiberAudit.lean` | `214882e014c0c0e7897d605ee7512403510f8bd11329ba95e3254efac03e1812` |
| `ActualTaggedVertexPresentationFiber.lean` | `2db76070b1a12710521d68f54f2d7230b4efece497a31a49549a5c546912f77c` |
| `ActualTaggedVertexPhysicalAcceptance.lean` | `232c4aa7c3068030eaf87b75e63c51227d43380b61ea10d57e786c188b31fd63` |
| `ActualTaggedVertexPhysicalLaw.lean` | `60641e139f23843ab38af4f45d565db1d100728dfeb1518b7fb354ab02e1c214` |
| `ActualTaggedVertexPhysicalLawChecks.lean` | `fa58f19c821970060a1199694b29d1d9d889c189591f1e67394055dfbcfc5492` |

The proof counts `2^(J*(2*h))` presentations per full tagged vertex, proves the class representative pushforward and its dependent product are uniform on full vertices, and proves physical acceptance invariant under a change of presentation for arbitrary fixed raw table, center table, and tagged star. Thus `taggedPhysicalMean_eq_vertexMean` is an exact fixed-star physical-law identity. It reduces the representative-law mismatch in the force comparison.

Open: the initial sampled full vertex and clique-resampled `U′` marginals have not been shown uniform under the manuscript's ordered star distribution; neither the quantitative collision bound nor MZ NO-soundness follows from this receipt. The arbitrary-weight `taggedPhysicalMass` wrapper has no separate certified equality to the vertex-law sum in this increment; its fixed-star summand equality is certified.
