# Actual Tree.parse FP complexity-theory review

**Verdict: GO**

Frozen source `52b57f29cd7d317bfa77a6d046f58ce3d44633a7`. Independently rehashed local main `563831C5485F44DE298A0E896BD6A9843F5B338F8CDA428F15DFBFB9EB057074` (git blob `701db566e3c5b2b9bede4b0940daeab88c64f779`, 33468 bytes), Checks `B9DA8EB5A89BDDA4F81FFA25D2B9D869E20B65978AD3A7ED8C344A131EDDBCA3` (git blob `eec2a3615324a2a939f5b7c5bab84513b7047911`, 996 bytes); objects `BEF82D9A5F18A1AB150C4945F370369654706539200555D47FD5437FE7D3F34F` / `3E17CACAAE1A4DF4AB37EF6FA62B53E167605BF8F0FA5F84E1ED5F5B26473D21`. Working tree at `6cdf45b` is byte-identical on both Lean files. Evidence `research/evidence/2026-09-16-actual-tree-parse-fp-fresh-run/` gate PASS naming `52b57f2`. `#print axioms` of `treeParseTag_mem_FP` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean. No leaf-star imports.

This increment is a genuine Cobham `FP` membership of a *total* packed `CMMSACodec.Tree.parse (|z|+1) z` transducer, including malformed and truncated inputs. It is not NP-hardness, not `paddedRun ∈ FP`, and not Theorem 1.

## Force

`treeParseTag : List Bool → List Bool` is the freeze packing of the existing semantic parser:

- `none` (empty tape, truncated `true`, leftover fuel-zero) ↦ `[]`;
- `some (t, rest)` ↦ `true :: pair (encode t) rest`.

`FP` here is Complexitylib’s TM class `{f | ∃ d k tm T, tm.ComputesInTime f T ∧ T =O (·^d)}`. Membership is not a custom machine and not `parse_encode` on well-formed trees. The witness is `Cobham.iterate_mem_FP` of an explicit one-bit stack step, transferred onto the spec by `mem_FP_of_eq`.

The stack machine is real recursive descent, not a dummy tag:

- Prefix binary trees: `leaf = [false]`, `node p q = true :: encode p ++ encode q`, matching `CMMSACodec.Tree.encode` / `Tree.parse`.
- Semantic state `(remaining, mode, stack)` with frames `needTwo` / `needOne p`. One `semStep` consumes at most one input bit; reduce reconstructs `encode (node p t) = true :: encode p ++ encode t`.
- Bit encoding of that state is pairing-block `pair remaining (pair mode stack)`. `parseStep` is assembled from `fstBlock` / `sndBlock`, `selectHead`, `emptyFlag`, `cons`, `append`, `dropLen`, and constants — all public Cobham closures. `parseStep_encode` is `parseStep (encodeState s) = encodeState (semStep s)` on every semantic state, so the FP step *is* the descent.

Iteration parameters are polynomial and used:

- Ruler `parseRuler z = (z ++ [false])^3` has length `3(|z|+1)`. That is the live clock, not the freeze’s sketch `|z|+1`. Init measure is `3|z|`; `iterate_ge_stuck` needs `measure + 1` steps, so `|z|+1` would be a miss and `3(|z|+1)` is the honest linear bound.
- Width `parseWidth z` has length `16(|z|+1)`. `Reach` keeps remaining a suffix of `z` and `modeBits + stackBits + |stack| + |remaining| ≤ |z|`; pairing overhead then fits in `16(n+1)`. `hbound` is exactly `iterate_mem_FP`’s hypothesis: every prefix of the init trajectory has length `≤ |width z|`.

Agreement with `Tree.parse` is for **every** `z`, not the well-formed fragment:

- `evalState (initSem z) = Tree.parse (|z|+1) z`;
- `evalState (semStep s) = evalState s`, using `parse_consumed` and `parse_fuel_ge` so nested fuel `|rest|+1` matches the spec’s depth fuel;
- after `|ruler z|` steps the state is stuck (`fail` or `success`);
- `packTag` of a stuck encoding is `[]` on `none` and `true :: pair (encode t) rest` on `some`.

`treeParseTag_eq_iter` is that chain. `treeParseTag_mem_FP` is `packTag ∘ parseStep^[|ruler|] ∘ initState` in `FP`, rewritten onto `treeParseTag`. Quantifiers are honest: `treeParseTag ∈ FP` is a total function fact, including garbage strings.

Concrete malformed cases are the spec, not extra restrictions. `Tree.parse 1 [] = none`. `Tree.parse 2 [true]` binds `parse 1 []` and is `none`. Fuel `0` is `none`; with start fuel `|z|+1` a string of unmatched `true`s hits fuel-zero or empty remaining and packs `[]`. Leftover *suffix after a complete tree* is packed as `rest`, which is what `Tree.parse` returns; it is not treated as hang.

## Packaging and theater

Module/commit titles that say “Tree.parse packed FP tag” name this transducer. `treeParseTag` is defined by matching `Tree.parse`, then proved equal to the iterate. That is spec-equals-impl, not a second function quietly in `FP`. `parseStep` does not call `Tree.parse`; the semantic evaluator is used only in the agreement proof.

This is a *prefix* parser. A successful tag can carry a nonempty `rest`. `decodeInput` additionally requires `rest = []` before `readInput`. Do not read `decodeInput ∈ FP` or “whole-string tree codec” off `treeParseTag_mem_FP`. The freeze packing is the prefix one; trailing-empty is the next Cobham obligation.

`decodeInputTag`, `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, and `selectedSeededMap` are absent. Freeze instruction after a genuine parse-only success is to stop there and not `sorry` the consumers. That is what compiled. `paddedRun` remains a Lean function from the prior policy module; there is still no `paddedRun ∈ FP`.

`hSrcCmmsa` is not inhabited. No 3SAT→`cmmsaPromise` `Preserves`, no table compiler, no HN/star compilation. No bound here feeds a switching-quality ratio. Do not read a randomized reduction, `PromiseNPHard`, or unconditional Theorem 1 off this membership.

The linear ruler `3(n+1)` and width `16(n+1)` are pairing/measure slack, not a claim of linear-time TM complexity. `iterate_mem_FP` supplies some polynomial; degree is not computed here and is not needed for `∈ FP`.

## Checks and non-credits

Checks `#check` / `#print axioms` of every public theorem: `treeParseTag`, `treeParseTag_empty`, `treeParseTag_none`, `treeParseTag_some`, `treeParseTag_leaf`, `treeParseTag_mem_FP`. Examples: `treeParseTag [] = []`, leaf `[false]` packs `true :: pair [false] []`, truncated `treeParseTag [true] = []` by `rfl`, and `treeParseTag ∈ Complexity.FP`. Axioms: empty/leaf axiom-free; none/some `propext`; membership the standard trio. No `#check decodeInputTag`, no `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`.

Fresh-run stages exception-repair / formula / cmmsa-codec / main×2 / checks×2 all exit 0. Independent rehash PASS, 61 rows, 0 mismatches. Source SHA-256 pins match the blobs above before and after every stage.

Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `decodeInput`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the total packed `Tree.parse` half of a future `decodeInputTag_mem_FP` (trailing-empty test on this tag, then `readInput` packing, `[]` on malformed). Next consumer remains that decoder, then `selectedPairedRun_mem_FP` / `selectedSeededMap`, then a 3SAT (or 3-Lin) → `encodeInput` compiler with `Preserves (1/6)`. Do not close the hardness route on this increment.
