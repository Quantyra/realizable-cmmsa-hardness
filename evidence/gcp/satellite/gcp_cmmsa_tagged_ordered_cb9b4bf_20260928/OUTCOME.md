# Tagged ordered star law: exact-source GCP receipt

- Source commit: `cb9b4bf`; uploaded source archive SHA-256: `f5a446aa68b9c794c658eb46c103caede3af0a1373da2a4481314fbc8752ec8c`.
- Receipt: `receipt.tar.gz`, SHA-256 `2ce3fb4de30db3383d84af4f714218272af4a758bb25575473a3a6d938a2e71a`.
- Isolated GCP checkout: `/home/dfredriksen_quantyra_org/cmmsa_tagged_ordered_cb9b4bf_exact` on `quantyra-lean-builder-01`.
- Two exact-source `lake build` runs passed, each with 3,232 jobs. Scoped `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. The forbidden-token scan was empty.
- The initial replay attempt after `lake clean` stalled while fetching a package from an inaccessible upstream and was terminated without a Lean compile. The replay succeeded after restoring a separate complete cache with the matching pinned manifest. The receipt contains the two successful build logs and source hash comparison.
- Source SHA-256 before and after both successful builds matched: `ActualTaggedConcreteStarLaw.lean` `63b3b835f389b6bdc3a1fc2c2c6c5a33feb19903684d5cfa0ccee70a1947ce97`; `ActualTaggedOrderedQuestionSourceBridge.lean` `95e66a951e403f2892dbd11dc451f540e033cb692f67b426d3565ae7e1a06c3c`; checks `93ef0e953c50d2f798f734c47b2c59c4ac65ba8eb75ab9367a9f2d818065bfa2`.
- Builder status after stop: `TERMINATED` (GCP `instances describe`, 2026-09-28).

The increment instantiates the arbitrary-fixed-table representative-selection comparison on a normalized ordered eligible tagged-U, conditional transverse-K, independent transverse-leaf law. It proves the ordered-U pushforward to uniform eligible row sets and derives eligible-U nonemptiness under the copied-source padding assumptions. The class-collision loss remains explicit.

This reduces the structural NO-soundness gap but does not provide a numerical NO bound. Conditional K and leaf nonemptiness remain hypotheses; the rank-`2h` leaf/domain pushforward and a quantitative class-collision bound at manuscript parameters remain unproved. The MZ NO decoder bound, Theorem 1, and Corollary 2 are not certified by this receipt.
