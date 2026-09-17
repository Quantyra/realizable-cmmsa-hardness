# Actual packed Tree.parse FP tag: non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `52b57f29cd7d317bfa77a6d046f58ce3d44633a7`. Gate logs name `52b57f2`, not `bba6dbb`. Main `ActualTreeParseFP.lean` SHA-256 `563831C5485F44DE298A0E896BD6A9843F5B338F8CDA428F15DFBFB9EB057074`. Checks SHA-256 `B9DA8EB5A89BDDA4F81FFA25D2B9D869E20B65978AD3A7ED8C344A131EDDBCA3`. Evidence `research/evidence/2026-09-16-actual-tree-parse-fp-fresh-run/`. Independently rehashed local sources at `52b57f2`, certify commit `6cdf45b`, `HEAD`, and the working tree match the freeze and the gate. Certification commit `6cdf45b` did not change the Lean sources.

Accepted, freeze stop-loss only (`treeParseTag ∈ Complexity.FP`; total, including malformed; no `decodeInputTag`, no `selectedPairedRun_mem_FP`, no `selectedSeededMap`, no `hSrcCmmsa`):

- `treeParseTag z` is the freeze packing of `CMMSACodec.Tree.parse (|z|+1) z` as `List Bool → List Bool`. Empty tape is `none` (malformed or truncated). Nonempty is `true :: pair (encode t) rest` for `some (t, rest)`.
- `treeParseTag_empty` is `treeParseTag [] = []`. `treeParseTag_none` / `treeParseTag_some` are the two match arms. `treeParseTag_leaf` is the well-formed leaf `[false]`.
- `treeParseTag_mem_FP` places that packed function in `Complexity.FP` from Cobham `iterate_mem_FP` of a total step, then `packTag`. The equality `treeParseTag_eq_iter` is for every `z`, not only `parse_encode` well-formed trees. It is not `Tree.parse : Nat → Bits → Option _ ∈ FP` (that type is not the Cobham carrier).
- `decodeInputTag` is not defined. There is no `decodeInputTag_mem_FP`, no `decodeInput ∈ FP`, and no `selectedPairedRun_mem_FP`.
- `selectedSeededMap` is not defined. `hSrcCmmsa` is not inhabited. There is no dummy 3SAT→CMMSA identity.

The module header denies `selectedSeededMap`, inhabited `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, and P vs NP. Checks `#check` / `#print axioms` only `treeParseTag`, `treeParseTag_empty`, `treeParseTag_none`, `treeParseTag_some`, `treeParseTag_leaf`, and `treeParseTag_mem_FP`; reduce `treeParseTag [] = []`, `treeParseTag [false]` against `treeParseTag_leaf`, and truncated `treeParseTag [true] = []`; and inhabit `treeParseTag ∈ Complexity.FP`. Checks do **not** `#check` `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, `selectedSeededMap`, or `hSrcCmmsa`. Main does not import `*Checks.lean`. `#print axioms treeParseTag_mem_FP` is `propext`, `Classical.choice`, `Quot.sound` only. Forbidden-scan is clean. README, `INTEGRITY-CLAIMS.md`, `CHANGELOG.md`, and `CITATION.cff` are unchanged by this increment.

Notes, not blocking:

- Module/commit titles that say "actual Tree.parse packed FP tag" are catalog labels. They name `treeParseTag ∈ Complexity.FP`, not the un-packed `Option`-valued parser, not `decodeInput ∈ FP`, not `selectedSeededMap`, not inhabited `hSrcCmmsa`, not unconditional Theorem 1, Corollary 2, publication, or `P` versus `NP`.
- Closeout phrasing "packed Tree.parse in FP" is the packing `treeParseTag`. Do not cite it as `Tree.parse ∈ FP` or as `decodeInput ∈ FP`.
- The truncated-`true` check is a runtime identity `treeParseTag [true] = []`, covered by the total packing (`none ↦ []`). It is not a named public theorem and is not an FP theorem about `decodeInput`.
- Stopping after `treeParseTag_mem_FP` is the freeze-permitted stop-loss. It does not expand the claim boundary to the rest of the SeededMap route.

Forbidden claims absent. The freeze’s `decodeInputTag` / `selectedPairedRun_mem_FP` / `selectedSeededMap` / `hSrcCmmsa` target remains open. Next: `decodeInputTag_mem_FP` (readInput packing after trailing-empty tests on `treeParseTag`), then `selectedPairedRun_mem_FP` and `selectedSeededMap`. Then a 3SAT (or 3-Lin) → `encodeInput` table compiler ∈ FP with `MapReducesVia` into a selected pipeline promise. Do not inhabit `hSrcCmmsa` with identity, do not sorry `decodeInputTag_mem_FP`, and do not skip to Theorem 1.
