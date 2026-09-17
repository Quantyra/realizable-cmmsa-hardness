# Actual readRatTag FP complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `dbdca8728e164f41d9fbe005ab699f48450c67f4` (`prove actual readRat packed FP tag`). Independently rehashed git blobs of Main `2508B3F45C37D04889D3B6448F0DAF44E8842F625B8D778D743E3A920D487763` (git blob `f1c8801e1e58edfa852904e018f0b762462926dd`, 95149 bytes, LF, git-object SHA-256 `9ED32D7441536EF3EE0F5B7814C425F7F2DA04071C3739E6852B1BA5A0AE5A1E`), Checks `9380B508A6BF71A74311AA8B6884921982D9B8CB3CB0DDC4D43FE80DC65E0B7A` (git blob `77e607bf3b607fb7b278d731da08ca178acfbc47`, 1248 bytes, LF, git-object SHA-256 `74E5DC78E74883AA13ABBDE3A9677C2C02516D324BB1AC37D5873BC6ADBE0B5C`). Oleans from the fresh-run `0F4729C564C61B7DF5B47091C59D826D3B13A7874553BEB0CDFD032D6EAC83DB` / `D22359AA6A705B5FB352C0A8573A5B1B113EEF59AC896DE0AC7369C3AB7A36C9`. Parent Lean blob for gcdBits remains `7fff1264a3d6de0eb5bb5857ea4f638222992a27` (`7105c95` / `c1292bb`); this commit adds 491 lines to Main and the Checks surface for `readRatTag_mem_FP`. HEAD git blobs equal the freeze. Local working-tree Main is *not* the freeze (109197 bytes, SHA-256 `90120560…`, extra content beyond CRLF); this review used only `git cat-file` blobs at `dbdca87`. Evidence `research/evidence/2026-09-16-actual-read-rat-fp-fresh-run/` gate PASS naming `dbdca87`. `#print axioms` of `readRatTag_mem_FP` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean. No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is a genuine Cobham `FP` membership of a *total* packed rational tag assembled from `gcdBits` / `dropTwos` / `packReduced` (plus `shareTwos`, `gcdPrep`, `quotBits`, digit encode). It is not `decodeInput ∈ FP`, not semantic `readRat` / `ratTree` agreement, and not Theorem 1.

## Force

`readRatTag : List Bool → List Bool` is the freeze packing of a complete-tree rational encoder, not a dummy constant and not a second function quietly swapped into `FP`:

- `treeParseTag z` empty → `[]`;
- leftover suffix after a parsed tree (`pairSnd (dropOne (treeParseTag z))` nonempty) → `[]`;
- else `readRatOnEncode` of the parsed encoding.

`readRatOnEncode` is a real field reader on a node: empty left digits, empty right digits, or den=0 after `stripTrailing ∘ dropOne` → `[]`; otherwise `packReduced` of those digit tapes. `packReduced a b` is

`[true, true] ++ encodeDigits (quotBits (pairFst (shareTwos a' b')) (gcdShared a' b')) ++ encodeDigits (quotBits (pairSnd (shareTwos a' b')) (gcdShared a' b'))`

with `a' = stripTrailing a`, `b' = stripTrailing b`. `[true, true] ++ encode p ++ encode q` is the `Tree.node` wire. `gcdShared = gcdBits ∘ gcdPrep ∘ shareTwos`. `dropTwos` is the inner `gcdStep` strip (`drop2Step^[|x|]`), already in `gcdBits`.

`FP` here is Complexitylib’s TM class `{f | ∃ d k tm T, tm.ComputesInTime f T ∧ T =O (·^d)}`. Membership is not a custom machine. `readRatTag_mem_FP` is public combinators only: `treeParseTag_mem_FP`, `dropOneFn_mem_FP`, `fstBlock` / `sndBlock`, `readRatOnEncode_mem_FP`, `emptyFlagFn_mem_FP`, `selectHeadFn_mem_FP`, `constFn_mem_FP`. It does not use `mem_FP_of_eq` to transport a different spec. The definition *is* the composition.

The inner witnesses are live polynomial iterates, not stuckness theorems:

- `gcdBits_mem_FP` remains `iterate_mem_FP gcdStep_mem_FP id_mem_FP gcdRuler_mem_FP gcdWidth_mem_FP hbound` then `fstBlock`; ruler `|z| ↦ 2|z|+16`, width `(2|z|+16)^2`.
- `shareTwos_mem_FP` is `iterate_mem_FP share2Step_mem_FP` with ruler `|a ++ b|` and width the pair itself; `share2Step` drops a common LSB `false` or stays.
- `gcdPrep` swaps an empty `pairFst` to `pair pairSnd pairFst`, so the prior `gcdBits (pair [] b) = []` stay-put does not fire on a zero numerator after sharing.
- `quotBits_mem_FP` is `divRunPair` (`divStep^[|a|+1]` long division) then reverse / `stripTrailing`; `DivReach` discharges quadratic `divWidth`.
- `encodeDigits_mem_FP` is `recFoldClamp` of the digit-tree fold with polynomial `4n+1`.
- `packReduced_mem_FP` is `appendFn` of those pieces (`maxHeartbeats 1000000` is a kernel budget, not a skipped goal).

Quantifiers are honest: `readRatTag ∈ FP` is a total function fact, including malformed trees, leftover bits, den=0, and garbage digit tapes. `id_mem_FP` is the Cobham stay-put branch, not a dummy 3SAT→CMMSA map.

The Stein-shaped dataflow is real, not ornamental: common factors of two are stripped *before* `gcdBits`, and `packReduced` quotients the *shared* tapes, so those 2s are already gone from numer/denom. `gcdPrep` is the empty-minuend correction named in the gcdBits review. That is composition of certified `gcdBits`, not a rewrite of `gcdBits` itself (`7fff1264` unchanged).

## Packaging and theater

Module/commit titles that say “readRat packed FP tag” name this transducer. `readRatTag` is *defined* as the `selectHead` / `readRatOnEncode` / `packReduced` composition, then proved in `FP`. That is spec-equals-impl for the packed function.

It is **not** semantic agreement with `CMMSACodec.readRat` or `CMMSAEncoding.ratTree`. There is no `readRatTag_of_tree`. Semantic `readRat` is `readNat n / readNat d` (reject den=0); `ratTree q` is `.node (natTree q.num.natAbs) (natTree q.den)` on Lean’s already-reduced `Rat`. The packed path *aims* at that reduced node via `gcdShared` / `quotBits`, but no theorem says `readRatTag (encode t) = []` or `true :: encode (ratTree q)` according as `readRat t`. `readNatTag_of_tree` exists and is unused by `readRatTag_mem_FP`. Do not read `readRat ∈ FP` or “quotBits = Nat.div / gcdBits = Nat.gcd” off this membership.

The `oddPart` / `gcdStep_oddPart` / `gcdStep_iterate_oddPart` block after `gcdBits_mem_FP` is unused by every `*_mem_FP` theorem. It is scaffolding toward a GCD identity that did not land. `gcdBits` is still `pairFst (gcdStep^[|gcdRuler|])`; the ruler is a polynomial clock, not a Stein fixed-point proof. `quotBits` is likewise a truncated divider, not a `Nat.div` identity.

Module header still says packed `decodeInput` as a total function in `FP`. The compiled public memberships are `gcdBits_mem_FP` and `readRatTag_mem_FP`. `decodeInputTag` is defined by matching semantic `decodeInput`. `decodeInputTag_mem_FP_of_read` is still a *conditional* lemma needing `readInputTag ∈ FP`. `readInputTag` is still a semantic `Tree.parse` / `readInput` matcher, not a Cobham assembly of `readRatTag`. So `readRatTag_mem_FP` does not discharge `decodeInputTag ∈ FP`.

`selectedPairedRun_mem_FP` and `selectedSeededMap` are absent as theorems. `ActualSelectedCmmsaSeededMap.lean` is untouched (`38d9ad0`, blob `9fa1a0ed`). Freeze stop-loss after a genuine `readRatTag_mem_FP`-only success is to stop and not `sorry` `decodeInputTag_mem_FP`. That is what compiled.

`hSrcCmmsa` is not inhabited. No 3SAT→`cmmsaPromise` `Preserves`, no table compiler, no HN/star compilation. No bound here feeds a switching-quality ratio. Do not read a randomized reduction, `PromiseNPHard`, or unconditional Theorem 1 off this membership.

Quadratic widths on gcd/div iterates are pairing/measure slack, not a claim of quadratic-time TM complexity. `iterate_mem_FP` supplies some polynomial; degree is not computed and is not needed for `∈ FP`.

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface: `decodeInputTag`, `decodeInputTag_empty`, `decodeInputTag_none`, `decodeInputTag_some`, `gcdBits`, `gcdBits_mem_FP`, `readRatTag`, `readRatTag_mem_FP`. Examples: `gcdBits ∈ Complexity.FP`, `readRatTag ∈ Complexity.FP`, `decodeInputTag [] = []`, truncated `decodeInputTag [true] = []` via `decodeInputTag_none`. Axioms: both memberships and the decode packing lemmas the standard trio. No `#check decodeInputTag_mem_FP`, no `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Checks header is the honest boundary (`gcdBits_mem_FP` and `readRatTag_mem_FP` on the Cobham surface; `decodeInputTag_mem_FP` remains).

Fresh-run stages exception-repair / formula / codec / randomized-reduction / assembly / tree-parse / main×2 / checks×2 all exit 0 (26 rows in `stage-exits.tsv`). Independent rehash PASS, 175 rows, 0 mismatches. Source SHA-256 pins match the blobs above before and after every stage. Bundle SHA-256 `F06511A2A11C1BF42C43B7850143835005DC60624435358184501BDF1DAA863F`.

Not `decodeInput ∈ FP`. Not `readRat ∈ FP`. Not semantic `ratTree` agreement. Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `readRatTag_of_tree`, `decodeInputTag_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the packed rational-tag half of a future `decodeInputTag_mem_FP` (semantic `readRatTag_of_tree` or an equivalent reduced-`ratTree` identity, then packed `readList` / `readFormula` / `readTable` / `readInputTag`, then the existing `decodeInputTag_mem_FP_of_read`). Next consumer remains that decoder, then `selectedPairedRun_mem_FP` / `selectedSeededMap`, then a 3SAT (or 3-Lin) → `encodeInput` compiler with `Preserves (1/6)`. Do not close the hardness route on this increment.

Notes: no HIGH false-force in the compiled theorem `readRatTag ∈ FP`. The notes are the documented limits: no `readRatTag_of_tree`, unused oddPart scaffolding, `gcdBits`/`quotBits` still iterates not number-theoretic identities, leftover module-header decodeInput-in-FP sentence, and `readInputTag` still semantic. Those limits do not make the Cobham composition theater.
