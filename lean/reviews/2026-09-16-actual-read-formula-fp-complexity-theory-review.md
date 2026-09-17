# Actual readFormulaTag FP complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `41c6e1ca1d4fc3d264d319fdd20cb65170b1851c` (`prove actual readFormula packed FP tag`). Parent `8aad0e122db97e69a9fb00bd0781c5239eb97e30` (`prove actual formStep_encode`). Independently rehashed git blobs of Main `ACD77A39B055A6F0630661D86D785BF256AE03B2FBDA15B682706373C9B09821` (git blob `ac96f44770354d3ab7a8799c4fa07d438ab5877e`, 264952 bytes, LF, git-object SHA-256 `B02DECD6794F6F1EE666213326A07287A5C344A7BCA0222B334DC51B1331DA61`), Checks `9200399532E217768D248356E9FDDC2E4346D4C3C5DB9A72BC1E5BB2C3025A60` (git blob `7d55f944c6432b1e7b5e00cc5fbda7ca9a5ec7f0`, 2680 bytes, LF, git-object SHA-256 `A49782BD899C73B071A19CB75A9E67E6A638A198DD57F889756EF34DD13899AC`). Parent Lean blobs `e74a0127efa37cb5f152bc78eba90855ec99cb75` / `ef5321f9286af69a449bb02e32f874e333174d1f` (262692 / 2536 bytes; SHA-256 `CB8735F4A4FBA6256FE4DF12CCA8A41B004BC6788267B5713C2EBFE3677FAD24` / `061E61D3FC20D65DBFD32163C613ACF1F651EEA87F1AA265EE4562099F0856CA`). Cert commit `0210ae9` adds evidence only; Lean blobs unchanged from `41c6e1c` (`git diff --name-only 41c6e1c HEAD -- '*.lean'` empty). Oleans independently rehashed from the frozen-target checkout `C118C1F7DDCD60180FB143CD571AD763F7318AC0E7B5AB9A9549AC7D6AABFA6E` / `12273BFE4B9EA38F8116DB27AB611B6079DFF87D8CB3DEF2EFD86EFC6480D048`, matching `formula-local-cert.txt`. This review used only `git cat-file` blobs at `41c6e1c`. Local working-tree Main/Checks are dirty (`git status --short` reports `M` on both; Main 273846 bytes, SHA-256 `755D1B0A…`, git `76b19233`, extra content beyond CRLF) and were not read as source. Evidence `research/evidence/2026-09-16-actual-read-formula-fp-fresh-run/` local target-fresh PASS naming `41c6e1c`; GCP builder reauth failed (`gcp-formula-unavailable.txt`). `#print axioms` of `readFormulaTag_mem_FP` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean (`sorry` / `native_decide` / `admit` / `axiom` count 0). `ActualSelectedCmmsaSeededMap.lean` untouched (`9fa1a0ed`). No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is a genuine Cobham `FP` membership of a *total* packed formula-stack iterate `formPack ∘ formStep^[|formRuler|] ∘ formInit`, with polynomial width discharged from `formula_encode_le` on the *parent* source tree, not `|left|+|right|`. It is not `decodeInput ∈ FP` and not Theorem 1.

## Force

`readFormulaTag : List Bool → List Bool` is the freeze packing of a complete-tree formula reader on `pair n.bits (encode t)`, not a dummy constant and not a second function quietly swapped into `FP`:

```lean
def readFormulaTag (z : List Bool) : List Bool :=
  formPack (formStep^[(formRuler z).length] (formInit z))
```

`FP` here is Complexitylib’s TM class `{f | ∃ d k tm T, tm.ComputesInTime f T ∧ T =O (·^d)}`. Membership is not a custom machine. The witness is public `Cobham.iterate_mem_FP formStep_mem_FP formInit_mem_FP formRuler_mem_FP formWidth_mem_FP hbound`, then `mem_FP_comp` with `formPack_mem_FP`. That is exactly the combinator’s conclusion `(fun z => F^[(ruler z).length] (init z)) ∈ FP` composed with the success packer. `readFormulaTag_mem_FP` does **not** use `mem_FP_of_eq` to transport a different spec. The definition *is* the iterate.

The stack machine is real recursive descent of `CMMSACodec.readFormula` / `CMMSAEncoding.formulaTree`, not a dummy tag:

- Prefix tags match the codec: var = `.node .leaf v`, and = `.node (.node .leaf .leaf) (.node p q)`, or = `.node (.node .leaf (.node .leaf .leaf)) (.node p q)`. Packed wrappers `wrapVarEnc` / `wrapAndEnc` / `wrapOrEnc` are the `Tree.encode` layouts `[true,false]++natEnc`, `[true,true,false,false,true]++p++q`, `[true,true,false,true,false,false,true]++p++q`, and `wrap*_eq` identifies them with `encode (formulaTree f)`.
- Semantic state `(bound, mode, stack)` with frames `waitRight` / `combine` carrying the *parent* source tree. One `formSemStep` either expands a var/and/or node or reduces a completed child. Fail/success stay put (`id_mem_FP` is that stay-put branch, not a dummy 3SAT→CMMSA map).
- Bit encoding is pairing-block `pair bound (pair mode stack)`. `formStep` is assembled from `fstBlock` / `sndBlock`, `selectHead`, `emptyFlag`, `eqFlag`, `splitNode`, `readNatTag`, `ltCanon`, `wrap*`, and constants — all public Cobham closures. `formStep_encode` is `formStep (encodeFormSem s) = encodeFormSem (formSemStep s)` on every semantic state, so the FP step *is* the descent. `formStep` does not call `readFormula`.
- Init parses `pairSnd z` with `treeParseTag` and rejects leftover suffix (decode-shaped complete tree). Bound is `pairFst z`.

The freeze blocker is width under iteration. Naive `|wrapAndEnc left right| = |left|+|right|+5` is not closed: `left`/`right` are already *canonical* `formulaTree` tapes, each allowed an `8|child|+8` blowup, so summing children at every combine is exponential in depth. The compiled invariant does **not** use that sum. `formReach_step` on `.combine` recovers `readFormula parent = some (and/or fl fq)` from `ctxOk` and applies

```lean
formula_encode_le (if isOr then .or fl fq else .and fl fq) parent hreadP
```

so the combined encoding is `≤ 8|parent|+8`. `stackOk` already has `|parent| ≤ |z|`, hence `enc.length ≤ 8|z|+8`. The var branch is the same lemma on `.node .leaf b`, not `|natTree k|`. `formula_encode_le` itself is an honest source-to-canonical comparison (`|formulaTree f| ≤ 8|encode t|+8` whenever `readFormula n t = some f`), with slack `21 ≤ 40` on the and-node arithmetic. That is the parent-width route the freeze named.

Iteration parameters are polynomial and used:

- Ruler `formRuler z = z ++ z ++ [false, false]` has length `2|z|+2`. It is a live clock for `iterate_mem_FP`. `FormReach.measure_le` keeps `formMeasure ≤ 2|z|+2`; `iterate_ge_formStuck` would make the semantic machine stuck after that many steps, but membership does not need stuckness.
- Width `formWidth z` has length `(2|z|+32)^3` via two `mulLenFn`. `FormReach` keeps `|bound| ≤ |z|`, stack depth `≤ 2|z|+2`, source trees `≤ |z|`, and canonical encodings `≤ 8|z|+8`. Pairing then fits in `80 n² + 300 n + 300 ≤ (2n+32)³` (`cube32_bound`). `hbound` is exactly `iterate_mem_FP`’s hypothesis: every prefix of the init trajectory has length `≤ |width z|`.
- `formReach_iterate` / `formStep_iterate_length` transfer that invariant onto the bit iterate through `formInit_eq` and `formStep_iterate_encode`. Every prefix is `encodeFormSem` of a `FormReach` state, including garbage tapes (parse-fail / leftover / malformed formula → `.fail`, short).

Quantifiers are honest: `readFormulaTag ∈ FP` is a total function fact, including malformed pairs, leftover bits, out-of-range variables, and garbage formula trees. Empty pack = none; nonempty = `true :: encode (formulaTree f)` only on the success flag.

## Packaging and theater

Module/commit titles that say “readFormula packed FP tag” name this iterate. `readFormulaTag` is *defined* as `formPack` of the `formStep` iterate, then proved in `FP`. That is spec-equals-impl for the iterate, not a second function quietly in `FP`. Parent `8aad0e1` already had `formStep_encode`, `formStep_mem_FP`, `formula_encode_le`, and a *commented* `formReach_step`…`readFormulaTag_mem_FP` draft whose comment said to use `formula_encode_le` on the parent. This commit uncomments and completes that draft. Freeze stop-loss after a genuine `readFormulaTag_mem_FP`-only success is to stop and not `sorry` `readFormulaTag_of_pair` / `decodeInputTag_mem_FP`. That is what compiled.

It is **not** semantic agreement with `CMMSACodec.readFormula` / `CMMSAEncoding.formulaTree`. There is no `readFormulaTag_of_pair`. Internal `evalForm` / `evalForm_step` / `pack_evalForm` / `formReaches` exist and would wire the stuck iterate to `readFormula`, but they are unused by `readFormulaTag_mem_FP`. Do not read `readFormula ∈ FP` off this membership. `FP` is a class of tape functions; the membership is `readFormulaTag ∈ FP`.

It is **not** `decodeInput ∈ FP`. `decodeInputTag` is still defined by matching semantic `decodeInput`. `decodeInputTag_mem_FP_of_read` remains a *conditional* lemma needing `readInputTag ∈ FP`. This commit adds no `readRow` / `readTable` / `readParameters` / `readInputTag_mem_FP`. Freeze next-consumers after this theorem are `readFormulaTag_of_pair` (optional, still open), then those field readers, then `decodeInputTag_mem_FP`.

It is **not** Theorem 1. `ActualSelectedCmmsaSeededMap.lean` blob `9fa1a0ed` is identical at parent and freeze. `hSrcCmmsa` / `selectedSeededMap` appear only as explicit non-claims in the module header. No `PromiseNPHard`, no table compiler, no HN/star compilation. No bound here feeds a switching-quality ratio.

Theater that this increment is *not*:

- Dummy 3SAT→CMMSA map. Absent.
- Width by `|left|+|right|`. The combine payload bound is `formula_encode_le` on the stored parent. `wrapAndEnc_length` exists and is unused by `formReach_step`.
- Spec restated as `readFormula` and then “proved” by `rfl` / `mem_FP_of_eq`. The public function is the bit iterate.
- `id_mem_FP` as a dummy reduction. It is fail/success stay-put.

`formWidth_mem_FP`’s `mem_FP_of_eq` only identifies `replicate (a³)` with the `mulLenFn` cube; that is the width tape, not a spec swap of `readFormulaTag`. Cubic `(2n+32)³` is pairing/measure slack, not a claim of cubic-time TM complexity. `iterate_mem_FP` supplies some polynomial; degree is not computed and is not needed for `∈ FP`.

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface: `decodeInputTag`, `decodeInputTag_empty`/`none`/`some`, `gcdBits`, `gcdBits_mem_FP`, `gcdBits_odd_pair`, `readRatTag`, `readRatTag_mem_FP`, `readRatTag_of_tree`, `readSignedTag`, `readSignedTag_mem_FP`, `readSignedTag_of_tree`, `readListTag`, `readListTag_mem_FP`, `readListTag_of_tree`, `readFormulaTag`, `readFormulaTag_mem_FP`. Examples: `gcdBits` / `readRatTag` / `readSignedTag` / `readListTag` / `readFormulaTag ∈ Complexity.FP`, leaf/`none` smoke tests for the earlier of-tree lemmas, `decodeInputTag [] = []`, truncated `decodeInputTag [true] = []` via `decodeInputTag_none`. Axioms: memberships, odd-pair GCD, of-tree identities, decode packing lemmas, and `readFormulaTag_mem_FP` the standard trio. No `#check readFormulaTag_of_pair`, no `#check decodeInputTag_mem_FP`, no `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Checks header is the honest boundary (`readFormulaTag` / `readFormulaTag_mem_FP` on the Cobham surface; `decodeInputTag_mem_FP` remains).

Local target-fresh of frozen `41c6e1c` blobs: main×2 exit 0 (olean `C118C1F7…`), checks×2 exit 0 (olean `12273BFE…`), `MATCH_MAIN=True MATCH_CHECKS=True`. Independent source SHA-256 pins match the closeout table. GCP instance start failed on reauth; certification is local-only.

Not `decodeInput ∈ FP`. Not `readFormula ∈ FP`. Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `readFormulaTag_of_pair`, `decodeInputTag_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the packed formula-tag half of a future `decodeInputTag_mem_FP` (semantic `readFormulaTag_of_pair` or an equivalent `formulaTree` identity, then packed `readRow` / `readTable` / `readParameters` / `readInputTag`, then the existing `decodeInputTag_mem_FP_of_read`). Next consumer remains that decoder, then `selectedPairedRun_mem_FP` / `selectedSeededMap`, then a 3SAT (or 3-Lin) → `encodeInput` compiler with `Preserves (1/6)`. Do not close the hardness route on this increment.

Notes: no HIGH false-force in the compiled theorem `readFormulaTag ∈ FP`. The iterate is a real formula stack machine; width is parent `formula_encode_le`, not child-sum theater. The notes are the documented limits: no `readFormulaTag_of_pair`, unused `evalForm`/stuckness scaffolding, cubic width slack, leftover module-header decodeInput-in-FP sentence, and local-only cert after GCP reauth failure. Those limits do not make the Cobham iterate membership theater.
