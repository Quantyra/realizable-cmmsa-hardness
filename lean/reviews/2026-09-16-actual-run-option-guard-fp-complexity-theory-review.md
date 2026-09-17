# Actual runOptionGuardTag FP complexity-theory review

**Verdict: GO-WITH-NOTES**

**Accepted:** packed `runOptionGuardTag ∈ Complexity.FP`.
**Not accepted / not credited:** unproved equality of the packed ruler to semantic `x.trials * x.precision`; un-packed `runOption ∈ FP`; `paddedRun ∈ FP`; `selectedPairedRun_mem_FP`; `runOptionTag_mem_FP`; Theorem 1.

Frozen source `c78bf1a5b4c8c31fe82535f3f293c57c2b348da2` (`prove actual runOptionGuard packed FP tag`). Git parent `374e1bad81688a6b27e115a5b9b1efa4a84f7dfd` (paddedRunGuard review); Lean parent of this module is still `b8ba7b55b542759d151410667ed56e50f6dcad3e` / `cba404e` (paddedRunGuard packed-FP freeze). Independently `git cat-file`’d and rehashed git blobs of Main `99B5245219A98031C9BA4537E19E2968FF29AD0327F41153CBF8B3275D5EB152` (git blob `7fe2f4c6bf7faffee4ea20d70b0cb108f57941a6`, 35975 bytes, LF, git-object SHA-256 `17EEC451530DB1EA822F093585252A9016E9DAC4075894BDC6BE386EEF3E3AD7`), Checks `FAF432B65CAC722C809646E2979EB8F2CEB43037D7018944C35DD64A055F38D8` (git blob `373bbdbd75f65f21c7b48867d973c600ea0dc224`, 2183 bytes, LF, git-object SHA-256 `62D903219F3547CE0852C2D70DA9047465C5F7A77A79B7E3F322E75FFF04D730`). Parent Lean blobs `de09577c74a2910aa2b81a360a5b4c3b5272878f` / `3f0fdc959eb9b333b79c142f4adc3a5cd3abd8c5` (14990 / 1759 bytes; SHA-256 `1B3BCB0452CD11DCB9C7B61E97F35FF8807297C0526F92534BF9DD2F3D7E69C9` / `94D888D4645D8BD0EB4231F2766F8878030CDC3C585AC06B4F3A0B055E3344A8`). Cert commit `01e599122f2a345e3c1cd4ab3bde3f35ef4d8d58` adds evidence only; Lean blobs unchanged from `c78bf1a` (`git diff --name-only c78bf1a 01e5991 -- '*.lean'` empty; same blob ids). This review used only `git cat-file` blobs at `c78bf1a`. Working-tree Main/Checks are byte-identical LF with the freeze hashes above. `MANUSCRIPT.md`, `README.md`, `CITATION.cff`, `lean/README.md`, `lean/PROVENANCE.md`, `lakefile.toml`, and `lean/PvNP.lean` are unchanged by this increment. Evidence `lean/evidence/2026-09-16-actual-run-option-guard-fp-fresh-run/` local target-fresh PASS naming `c78bf1a`; GCP builder TERMINATED idle-stopped (`gcp-run-option-guard-unavailable.txt`). Recorded oleans `960B9AB41DA7C6BF5621A2BB285FA926A1D43F34AEE63E2E5AF7352F7BFB1651` / `6C841EBD06E28B9E470E600F26517364C4A270E49083B5A1F8B630BCC8CD4B9B` (main+Checks twice, matching hashes, exit 0) are taken from that cert log; this lens did not rebuild. `#print axioms` of `runOptionGuardTag_mem_FP` / `runOptionGuardTag_none` / `runOptionGuardTag_empty` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean on the freeze Main and Checks blobs (`sorry` / `native_decide` / `admit` / `axiom` count 0). No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is a genuine Cobham `FP` membership of the packed decode + length-guard transducer `runOptionGuardTag`: parent `decodeInputTag` on `pairFst`, a unary walk of the packed `natTree` encodings of the precision/trials fields, `mulLenFn` of those unary lengths as a coin-tape ruler, and `lenEqFlag` against `pairSnd`. Success payload is `true :: pair instanceBits coins`; malformed decode is `[]`. It is not a dummy constant, not an identity reduction, and not a spec-matcher for `runOption`. It is not un-packed semantic `runOption ∈ FP`, not `paddedRun ∈ FP`, not `selectedPairedRun_mem_FP`, and not Theorem 1. Do not credit an unproved equality of the packed ruler length to semantic `trials * precision`.

## Force

The compiled public theorems of this increment are exactly the freeze statements:

```lean
theorem runOptionGuardTag_mem_FP : runOptionGuardTag ∈ Complexity.FP

theorem runOptionGuardTag_none (z : List Bool)
    (h : decodeInput (pairFst z) = none) :
    runOptionGuardTag z = []

theorem runOptionGuardTag_empty : runOptionGuardTag [] = []
```

There is no `runOptionGuardTag_eq`. Closeout “Next consumer” names that identity, then packed `checkedBits` / `accepted` / `tree` / `bits`, then `runOptionTag_mem_FP` and `selectedPairedRun_mem_FP`. That is the remaining packing contract, not a theorem of this freeze.

`runOptionGuardTag` is the packed tape function

```lean
def runOptionGuardTag (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (instTag z)) []
    (Cobham.selectHead
      (Cobham.lenEqFlag (pairSnd z) (trialsPrecisionRuler z))
      (true :: pair (pairFst z) (pairSnd z))
      [])
```

with `instTag z = decodeInputTag (pairFst z)` and

```lean
private def trialsPrecisionRuler (z : List Bool) : List Bool :=
  List.replicate ((precisionUnary z).length * (trialsUnary z).length) false
```

`FP` here is Complexitylib’s TM class `{f | ∃ d k tm T, tm.ComputesInTime f T ∧ T =O (·^d)}`. Membership is not a custom machine and not a new complexity axiom.

That is a real packing of the *decode + coin-length* conjuncts of semantic `runOption`:

```lean
def runOption (L : Nat) (instanceBits coins : Bits) : Option Bits := do
  let x ← decodeInput instanceBits
  if h : coins.length = x.trials*x.precision then
    ExecutablePipeline.checkedBits L x.weights x.source x.precision x.trials x.parameters
      (seedsOf x.trials x.precision coins h)
  else none
```

On a paired tape `z`, `pairFst z` is `instanceBits` and `pairSnd z` is `coins`. The freeze tag implements the first bind and a length-equality test of the coin tape against a Cobham ruler assembled from packed field encodings. On success it re-emits the guarded pair rather than calling `checkedBits`. Failure of decode is the same Cobham `[]` convention as `decodeInputTag`. It is not a dummy constant and not an identity reduction.

The length-guard transducer is a unary walk, not a `Nat` field projection:

- `precisionEnc` / `trialsEnc` are the parent `inputTree` field probes: `nodeLeft` / `nodeRight` of `encodeInput x = Tree.encode (.node weights (.node rows (.node params (.node (natTree precision) (natTree trials)))))`. On `decodeInput (pairFst z) = some x`, `precisionEnc_some` / `trialsEnc_some` are compiled identities onto `Tree.encode (natTree x.precision)` / `Tree.encode (natTree x.trials)`.
- `natTree n = digitTree n.bits` with `digitTree [] = .leaf`, `false :: bs ↦ .node .leaf (digitTree bs)`, `true :: bs ↦ .node (.node .leaf .leaf) (digitTree bs)`. `Tree.encode` is concatenation (`.leaf ↦ [false]`, `.node p q ↦ true :: encode p ++ encode q`), so the digit tags are exactly `[false]` and `[true, false, false]`.
- `splitNode` reparses that concatenation through `treeParseTag` into a Complexity `pair`, so `nodeLeft` / `nodeRight` recover `encode p` / `encode q`.
- `nuStep` is one LSB digit of that encoding: stay if `nuFlag` is already nonempty; `nuDone` if `nuRem = [false]`; `nuFail` if `splitNode` is empty or the left tag is neither digit; `nuFalseDigit` doubles `nuPow` (clamped); `nuTrueDigit` adds current `nuPow` into `nuAcc` then doubles (both clamped). Init is `nuPack coinsCap enc [] [false] []` with `coinsCap = pairSnd z ++ [false]` (unary cap `coins.length+1`) and `nuPow` length 1.
- `nuRunEnc enc z = nuStep^[(nuIterRuler z).length] (nuInitEnc enc z)` with clock `|z| + |decodeInputTag (pairFst z)| + 1`. `natUnaryEnc` emits `nuAcc` only on success flag `[false]`; empty or fail flag packs `[]`.
- `precisionUnary` / `trialsUnary` are that walk on `precisionEnc` / `trialsEnc`. `trialsPrecisionRuler` is `mulLenFn` of those unary *lengths*. `lenEqFlag` tests `|pairSnd z|` against that product.

`runOptionGuardTag_mem_FP` is that algebra:

- `instTag_mem_FP` is `mem_FP_comp Cobham.fstBlock_mem_FP decodeInputTag_mem_FP`;
- coins tape is `Cobham.sndBlock_mem_FP`;
- `precisionEnc_mem_FP` / `trialsEnc_mem_FP` are nested `nodeLeft` / `nodeRight` of `instEnc`;
- `nuStep_mem_FP` is nested `selectHeadFn` / `emptyFlagFn` / `eqFlagFn` / `splitNode` / `nuPack` / `takeLen` (`nuClamp`) on those projections;
- `precisionRun_mem_FP` / `trialsRun_mem_FP` are `Cobham.iterate_mem_FP nuStep_mem_FP (nuInitEnc_mem_FP ·) nuIterRuler_mem_FP nuWidth_mem_FP hbound`, with `NuReach` discharging `|st| ≤ |nuWidth z| = 16·(|z| + |decodeInputTag| + |coinsCap| + 1)` on every prefix;
- `precisionUnary_mem_FP` / `trialsUnary_mem_FP` are `natUnaryEnc_mem_FP` of those iterates;
- ruler is `Cobham.mulLenFn_mem_FP precisionUnary_mem_FP trialsUnary_mem_FP`;
- length equality is the local `lenEqFlagFn_mem_FP` (`andBitFn_mem_FP` of two `lenLeFlagFn_mem_FP`);
- success payload is `mem_FP_comp` of `Cobham.pairFn_mem_FP fstBlock_mem_FP sndBlock_mem_FP` with `Cobham.cons_mem_FP true`;
- outer/inner choice is `Cobham.selectHeadFn_mem_FP` on `emptyFlagFn_mem_FP instTag_mem_FP` and on the length flag, against `constFn_mem_FP []`.

No new combinator. `decodeInputTag_mem_FP` is the parent decodeInput freeze (`f7f338b`). The unary iterate is new in this module and is used, not restated as a complexity axiom. Polynomial time is in `|z|`: the unary accumulators are clamped to `coins.length+1`, so the walk never materializes a tape of semantic numeric `trials` or `precision`.

`runOptionGuardTag_none` is the decode-failure branch only (`instTag = []` → `emptyFlag_nil` → `[]`). `runOptionGuardTag_empty` is that lemma at `[]` via `decodeInput_empty`. Quantifiers on those two lemmas are honest for every `z` with `decodeInput (pairFst z) = none`. They do **not** identify the success branch with `coins.length = x.trials * x.precision`.

Together: a total Cobham-`FP` tape function, on every bitstring, outputs `[]` or `true :: pair instanceBits coins` according as decode fails or the packed unary-product length guard fails, versus both succeeding. Do not read un-packed `runOption ∈ FP` off this: `FP` is a class of tape functions; the membership is `runOptionGuardTag ∈ FP`. Do not read `|trialsPrecisionRuler z| = x.trials * x.precision` off the membership: that identity is not compiled.

No bound here feeds a switching-quality ratio. No 3SAT→`cmmsaPromise` `Preserves`. No `hSrcCmmsa` inhabitation.

## Packaging and theater

Module/commit titles that say “runOptionGuard packed FP tag” name this composition. Checks header moves `runOptionGuardTag` / `runOptionGuardTag_mem_FP` / `runOptionGuardTag_none` / `runOptionGuardTag_empty` onto the Cobham/semantic surface and records that `decodeInputTag_mem_FP` is available. The remaining gap is named as `selectedPairedRun_mem_FP` / `selectedSeededMap`: `checkedBits` / `accepted` / output `tree` are not packed. That matches the stop-loss after the parent paddedRunGuard packing: pack the `runOption` decode + length-guard transducer, stop before the executor. That is what compiled.

It is **not** un-packed semantic `runOption ∈ FP` as a named machine class beyond the tag. `runOption` remains the `Option Bits` parser/executor in `ExecutablePipelineInput.lean`. There is no `runOption_mem_FP` and no `runOptionTag_mem_FP`.

It is **not** `paddedRun ∈ FP`. `paddedRun` / `paddedRunOption` remain in `ExecutableSamplingPolicy.lean`. Parent `paddedRunGuardTag_mem_FP` still packs only decode + `coinRuler` length, not this field-derived ruler.

It is **not** `selectedPairedRun_mem_FP`. `selectedPairedRun` is still the parent Lean wrapper `paddedRun L eps (pairFst z) (pairSnd z)` with no membership theorem. Header still omits it because `checkedBits` / `accepted` / output `tree` are not packed.

It is **not** `selectedSeededMap` and **not** Theorem 1. `hSrcCmmsa` / `selectedSeededMap` appear only as explicit non-claims in the module header. No `PromiseNPHard`, no table compiler, no HN/star compilation.

Theater that this increment is *not*:

- Dummy 3SAT→CMMSA map. Absent.
- A spec-matcher `runOptionGuardTag` defined by matching `runOption` and then “proved” in `FP` by `rfl`. The freeze function is nested `selectHead` / `emptyFlag` / `lenEqFlag` on `instTag` and a `mulLenFn` ruler of two unary iterates.
- Identity reduction: decode-failure is `[]`; success re-emits `true :: pair instanceBits coins`, not `id`.
- Spec restated as a new function already equal to `runOption` with no guard walk. Decode is the parent `decodeInputTag`; precision/trials are packed `natTree` encodings; the ruler is an iterate of `nuStep` plus `mulLenFn`; length equality is `lenEqFlag`.
- A new complexity axiom. Membership uses the existing combinators named above. Local `lenEqFlagFn_mem_FP` is `andBitFn_mem_FP` of two `lenLeFlagFn_mem_FP`. `iterate_mem_FP` is the parent Cobham iterator; `NuReach` is a length invariant, not a semantic stuckness theorem.
- A dummy unary walk that ignores the encodings. `nuStep`’s digit tags are the `digitTree` encodings; `precisionEnc_some` / `trialsEnc_some` feed `encode (natTree ·)` on successful decode. Init `nuPow = [false]` is LSB `2^0`. That is a real binary-to-unary transducer of the packed fields, clamped to the coin tape.

Domain note (the “notes” in the verdict, not a hole in `runOptionGuardTag_mem_FP`): there is no compiled identity

```lean
precisionUnary z = List.replicate x.precision false
trialsUnary z    = List.replicate x.trials false
(trialsPrecisionRuler z).length = x.trials * x.precision
```

nor a `runOptionGuardTag_eq` rewriting the success branch to `coins.length = x.trials * x.precision`. Fuel sufficiency of `|nuIterRuler z|` against `|natTree n|`, exactness of the LSB walk on well-formed `digitTree`, and the claim that clamping to `coins.length+1` preserves *equality* vs semantic `trials*precision` are all unproved. Docstring/closeout phrasing “unary `trials*precision` length guard” names the *intended* packing of `runOption`’s length conjunct. It is not a kernel theorem. Do not credit it.

Private `weightsLenBits` / `rowsLenBits` (and their `_mem_FP` / `_some` lemmas) remain unused by `runOptionGuardTag`. That is leftover scaffolding toward remaining `paddedRunOption` policy-field guards, not a second function quietly swapped into `FP`.

`ActualSatToThreeSatSource` remains imported and opened; no theorem of this increment uses it. Leftover hardness packaging, not a dummy reduction.

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface, including prior `selectedCoinRuler_mem_FP` / `paddedRunGuardTag_mem_FP` / `paddedRunGuardTag_eq` and the new `runOptionGuardTag` / `runOptionGuardTag_mem_FP` / `runOptionGuardTag_none` / `runOptionGuardTag_empty`. Examples: ruler length `= coinRuler`, empty paired run `selectedPairedRun L (1/4) [] = []`, `selectedCoinRuler eps ∈ Complexity.FP`, `paddedRunGuardTag eps ∈ Complexity.FP`, empty-tape `paddedRunGuardTag eps [] = []`, `runOptionGuardTag ∈ Complexity.FP`, empty-tape `runOptionGuardTag [] = []`. Axioms: memberships and identities the standard trio. No `#check selectedPairedRun_mem_FP`, no `#check runOptionTag_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Checks header is the honest boundary. Smoke tests are the failure branch (empty tape); there is no Checks roundtrip that a well-formed `encodeInput` paired with a `trials*precision`-length coin tape packs `true :: pair instanceBits coins`.

Local target-fresh of frozen `c78bf1a` blobs (cert log): main×2 exit 0 (olean `960B9AB41DA7C6BF5621A2BB285FA926A1D43F34AEE63E2E5AF7352F7BFB1651`), checks×2 exit 0 (olean `6C841EBD06E28B9E470E600F26517364C4A270E49083B5A1F8B630BCC8CD4B9B`), `MATCH_MAIN=True MATCH_CHECKS=True`. Independent source SHA-256 pins match the closeout table. GCP instance TERMINATED after the previous increment; manuscript-repo content-addressed cloud gate is not ported; certification is local-only. Closeout SHA-256 `25FB6706B5E5D8C263BDDAF60B90C5D6CC17D2F7536C99BF9C310777BEEBE9AF` (git blob `7c4070a0dc10a2afca6feedf1e9cf3b8c2094d27`, 1555 bytes, LF). Local cert log SHA-256 `F73488C4A2B956DF7F601A2F77FDB92BF4A13C9C9F572EF084BBA807EFAC3DE1` (git blob `efee833ac1a6b49ad560522386cbe28c799edf4e`, 3169 bytes, LF). GCP unavailability note SHA-256 `6883DCE49FE60603F475EAA02807354CCA47CE6F8E4F9B813252276390615A7D` (git blob `626fa85db99019cc86acf62e419658ef47a08f5e`, 365 bytes, LF).

Not un-packed `runOption ∈ FP`. Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: semantic `|trialsPrecisionRuler z| = x.trials * x.precision`, `runOptionGuardTag_eq`, `runOptionTag_mem_FP`, `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the decode + packed-length-guard half of a future `runOptionTag_mem_FP` (still needs a proved `runOptionGuardTag_eq` onto semantic `trials*precision`, then Cobham packing of `checkedBits` / `accepted` / output `tree`, then `selectedPairedRun_mem_FP`, then `selectedSeededMap`, then a 3SAT or 3-Lin → `encodeInput` compiler with `Preserves (1/6)`). Do not close the hardness route on this increment. Do not inhabit `hSrcCmmsa` with identity.

Notes: no HIGH false-force in the compiled theorem `runOptionGuardTag ∈ FP`. The packing is a real combinator walk already in `FP`: parent `decodeInputTag`, packed `natTree` field encodings, a clamped LSB unary iterate, `mulLenFn` of those unary lengths, `lenEqFlag` of the coin tape against that ruler, `selectHead` onto `true :: pair instanceBits coins` or `[]`. The notes are the documented limits: unproved equality of that ruler to semantic `trials*precision` (do not credit it), no `runOptionGuardTag_eq`, Checks smoke-test only the empty-tape failure, unused `weightsLenBits` / `rowsLenBits` scaffolding, leftover `ActualSatToThreeSatSource` import, local-only cert after GCP idle-stop, and leftover hardness packaging toward `selectedPairedRun_mem_FP`. Those limits do not make the packed membership theater.
