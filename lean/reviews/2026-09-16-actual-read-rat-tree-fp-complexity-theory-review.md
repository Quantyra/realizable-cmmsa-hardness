# Actual readRatTag tree-agreement complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `93d35131ed5317209ab456651387d4d9a2558fc2` (`prove actual readRatTag tree agreement`). Parent `91d8de75aa028847c37b57f0c0fabb302959d2b9` (`prove actual gcdBits odd-pair semantics`). Independently rehashed git blobs of Main `6356E80AF6A35BF9725434C911961B130A2BAD86F46B42951A7E2D85FB2907D4` (git blob `c32c15224f13c7196fa4491991ca6f10cffbe2bc`, 149949 bytes, LF, git-object SHA-256 `A13687A20DECB27E902380A15E6F67697F33366CCA6B54B9DC00F5168F5FED24`), Checks `0EA0879E4232070A818E453FB0885A1934BFC29709391DA022817038088593E1` (git blob `0943f4d1fe396732764c44ebbab0c8d54b807d20`, 1583 bytes, LF, git-object SHA-256 `28E39315D3A17F0320F8A31371869810CB00431C7A121B4A99A936D8179593C9`). Parent Lean blobs `ef6e01beed60801771de756c718657929782621c` / `2d5de2ccd4e13e7550d1b75c7393170f6fcfd2f8` (139080 / 1348 bytes; SHA-256 `C6ADF5EAD59BF17675B0B2F22BA1183DB37AEEAF27C41C1C793F5E5CF6D3E190` / `380D014789BD3ED5A07AF39F2C68158FE51B6D658B4F9DED6915254DF2A6282B`). Cert commits `4ca1d89` / `453fdf4` add evidence only; Lean blobs unchanged from `93d3513` (`git diff --name-only 93d3513 HEAD -- '*.lean'` empty). Oleans from the local fresh-run `825FD451B5E459A111AAEC37238062F373E9FEE1869DA4A373341E91F6DA1BFB` / `F6DFD04AD74F078DA70BE8F9FDECE26F07F9B4711882585EB1522F09A6AEC209`. This review used only `git cat-file` blobs at `93d3513`. Local working-tree Main/Checks are dirty (`git status --short` reports `M` on both; extra content beyond CRLF) and were not read as source. Evidence `research/evidence/2026-09-16-actual-read-rat-tree-fp-fresh-run/` local target-fresh PASS naming `93d3513`; GCP builder reauth failed (`gcp-of-tree-unavailable.log`). `#print axioms` of `readRatTag_of_tree` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean (`sorry` / `native_decide` / `admit` / `axiom` count 0). `ActualSelectedCmmsaSeededMap.lean` untouched (`9fa1a0ed`). No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is genuine semantic agreement of the already-packed Cobham tag `readRatTag` with `CMMSACodec.readRat` / `CMMSAEncoding.ratTree` on complete tree encodings. It is not `decodeInput ∈ FP` and not Theorem 1.

## Force

The compiled public theorem is exactly the freeze statement:

```lean
theorem readRatTag_of_tree (t : CMMSACodec.Tree) :
    readRatTag (CMMSACodec.Tree.encode t) =
      match CMMSACodec.readRat t with
      | none => []
      | some q => true :: CMMSACodec.Tree.encode (CMMSAEncoding.ratTree q)
```

Quantifiers are honest: the identity is for every complete encoding `encode t`, including leaves, malformed field trees, and den=0. It is not a well-formed-only fragment and not a dummy constant. Semantic `readRat` (`CMMSACodec.lean`) is `readNat n / readNat d` on `.node n d`, rejecting non-nodes and den=0. Semantic `ratTree q` is `.node (natTree q.num.natAbs) (natTree q.den)` on Lean’s already-reduced `Rat`. The packed path is proved to emit that reduced node (success-prefixed) or `[]`.

This commit does **not** redefine `readRatTag` / `packReduced` / `gcdShared`. Those definitions are unchanged from the parent `readRatTag_mem_FP` increment. The new content is an identity chain on that existing transducer:

1. `readRatTag (encode t)` reduces to `readRatOnEncode (encode t)` because `treeParseTag_encode_append t []` packs `true :: pair (encode t) []` (empty leftover). Trailing-nonempty tapes still map to `[]` by the old `selectHead` on `pairSnd`; that is decode-shaped, not a silent prefix reader.
2. `readRatOnEncode_of_tree` cases the codec reader: leaf / `readDigits` fail / den=0 after `stripTrailing` → `[]`; otherwise `packReduced` of the digit tapes.
3. `packReduced_eq` is the number-theoretic reconstruction, not packaging:
   - `shareTwos_spec` gives `a = a' * 2^k`, `b = b' * 2^k`, and stuckness `a'=[] ∨ b'=[] ∨ odd a' ∨ odd b'`.
   - `gcdShared_eq` (canonical bits) feeds that stuckness into `gcdPrep` / `gcdBits_odd_pair` / `gcdBits_of_fixed`, so the packed GCD of the *remaining* parts is `Nat.gcd(a',b').bits`. Empty-minuend is the `gcdPrep` swap: `gcdBits (pair [] b)` stay-put does not fire; `gcd(0,b')=b'`.
   - `quotBits_eq` is a live `Nat.div` identity (`divInv` remainder `<` divisor), not a truncated-divider slogan.
   - `gcd(a0,b0) = gcd(a',b') * 2^k` restores the 2s that `gcdBits` itself does not extract, so
     `a0 / gcd(a0,b0) = a' / gcd(a',b')` and likewise for `b`. That is classical Stein reconstruction of the reduced fraction.
   - `rat_num_den_of_nat` identifies those quotients with `((n:Rat)/d).num.natAbs` and `.den`.
   - `encodeDigits_eq` / `natTree` wire the digit tapes as `Tree.encode (ratTree ((bitValue a : Rat) / bitValue b))`.
   - The `[true, true] ++ encode num ++ encode den` layout is success-bit plus `node` tag, i.e. `true :: encode (ratTree q)`, matching the freeze packing.
4. Digit-tape canonicity is discharged: `readDigitsTag_of_tree` supplies the codec’s raw bits; `stripTrailing_eq_bits` puts `packReduced_eq` on `n.bits` form. Non-canonical trailing zeros in a digit list are stripped before GCD/div, so the output is `n.bits`, not a padded alias.

`gcdBits` remains the subtractive iterate from the earlier FP increment and is still not classical Stein by itself. `gcdShared = gcdBits ∘ gcdPrep ∘ shareTwos` **is** the missing Stein wrapper, and `gcdShared_eq` is the `Nat.gcd` identity on the remaining parts. Combined with `quotBits_eq`, the packed tag computes Lean’s reduced rational tree. That is real semantic agreement of an `FP` function with the codec, not a second function quietly swapped into `FP` via `mem_FP_of_eq`.

Together with the parent `readRatTag_mem_FP`, the complexity content is: a total Cobham-`FP` tape function, restricted to the image of `Tree.encode`, outputs the encoding of the reduced `ratTree` or `[]` according as `readRat`. Do not read `readRat ∈ FP` off this: `FP` is a class of tape functions; the membership is `readRatTag ∈ FP`, and this theorem is agreement on encodings.

No bound here feeds a switching-quality ratio. No 3SAT→`cmmsaPromise` `Preserves`. No `hSrcCmmsa` inhabitation.

## Packaging and theater

Module/commit titles that say “readRatTag tree agreement” name this identity. Checks header moves `readRatTag_of_tree` onto the Cobham/semantic surface and keeps `decodeInputTag_mem_FP` as remaining. That matches the freeze stop-loss: if `readRatTag_of_tree` lands, commit it and do not `sorry` the decoder.

It is **not** `decodeInput ∈ FP`. `readInputTag` is still a semantic `Tree.parse` / `readInput` matcher. `decodeInputTag_mem_FP_of_read` remains a *conditional* lemma needing `readInputTag ∈ FP`. `decodeInputTag` is still defined by matching semantic `decodeInput`. This commit adds no `readSigned` / `readList` / `readFormula` / `readTable` packing. Freeze next-consumers after this theorem are those field readers, then `readInputTag_mem_FP`, then `decodeInputTag_mem_FP`.

It is **not** Theorem 1. `ActualSelectedCmmsaSeededMap.lean` blob `9fa1a0ed` is identical at parent and freeze. `hSrcCmmsa` / `selectedSeededMap` appear only as explicit non-claims in the module header. No `PromiseNPHard`, no table compiler, no HN/star compilation.

Theater that this increment is *not*:

- Dummy 3SAT→CMMSA map. Absent.
- Spec restated as a new function already equal to `ratTree` and then “proved” by `rfl`. `packReduced` is still the share/gcd/quot/encode composition; `packReduced_eq` is a calculation through `Nat.gcd`, `Nat.div`, and `Rat.num`/`Rat.den`.
- `gcdBits_odd_pair` used as a slogan. `gcdShared_eq` actually applies it under the `shareTwos` stuckness hypotheses (nonempty first component after `gcdPrep`, at least one odd or a zero second component).
- Claiming `Nat.gcd ∈ FP` or `readRat ∈ FP`. Membership theorems are unchanged; this is agreement.

`maxHeartbeats 800000` on `packReduced_eq` is a kernel budget, not a skipped goal. Unused `simp` arguments in the of-tree cases (`selectHead_true` / `selectHead_false`) are lints recorded in the local cert log; they do not alter the identity.

Domain note (the “notes” in the verdict, not a hole in the theorem): agreement is on `encode t`, not on arbitrary tapes. A valid rat-tree prefix with leftover suffix still packs `[]`, because `readRatTag` requires empty `pairSnd` after `treeParseTag`. That matches `decodeInput`’s trailing-empty guard. Do not quote this theorem as “packed readRat of every prefix.”

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface: `decodeInputTag`, `decodeInputTag_empty`/`none`/`some`, `gcdBits`, `gcdBits_mem_FP`, `gcdBits_odd_pair`, `readRatTag`, `readRatTag_mem_FP`, `readRatTag_of_tree`. Examples: `gcdBits ∈ Complexity.FP`, `readRatTag ∈ Complexity.FP`, `readRatTag (encode leaf) = []` via `readRatTag_of_tree`, `decodeInputTag [] = []`, truncated `decodeInputTag [true] = []` via `decodeInputTag_none`. Axioms: memberships, odd-pair GCD, tree agreement, and the decode packing lemmas the standard trio. No `#check decodeInputTag_mem_FP`, no `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Checks header is the honest boundary.

Local target-fresh of frozen `93d3513` blobs: main×2 exit 0 (olean `825FD451…`), checks×2 exit 0 (olean `F6DFD04A…`), `MATCH_MAIN=True MATCH_CHECKS=True`. Independent source SHA-256 pins match the closeout table. Bundle SHA-256 recorded there `3BE4A9BE96181EA7536E5C6E2580D0BD8AED32FE999642C589418C3F0B36A664`. GCP instance start failed on reauth; certification is local-only.

Not `decodeInput ∈ FP`. Not `readRat ∈ FP`. Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `decodeInputTag_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the semantic half of a future `decodeInputTag_mem_FP` (packed `readList` / `readFormula` / `readTable` / `readInputTag` on this rat agreement, then the existing `decodeInputTag_mem_FP_of_read`). Next consumer remains that decoder, then `selectedPairedRun_mem_FP` / `selectedSeededMap`, then a 3SAT (or 3-Lin) → `encodeInput` compiler with `Preserves (1/6)`. Do not close the hardness route on this increment.

Notes: no HIGH false-force in the compiled theorem `readRatTag_of_tree`. The identity is real Stein/div reconstruction of Lean’s reduced `ratTree`, on the same packed function already in `FP`. The notes are the documented limits: complete-tree domain (leftover suffix → `[]`), Checks smoke-test only the leaf/`none` branch, local-only cert after GCP reauth failure, leftover module packaging toward `decodeInputTag ∈ FP`, and unused simp lints. Those limits do not make the agreement theater.
