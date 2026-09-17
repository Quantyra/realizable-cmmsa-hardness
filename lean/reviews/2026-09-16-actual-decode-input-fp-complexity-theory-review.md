# Actual decodeInputTag FP complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `f7f338bdd28101ff66fa482716a435ca783cd191` (`prove actual decodeInput packed FP tag`). Parent `98ffac04e6e9ce96db5690e47aa3143c927ef568` (certified companion of `readTableTag_of_rows` / `a591714`+`f5995f2`). Independently rehashed git blobs of Main `D2405DC2CE759190671801AEF669297C1F8DD9F56BAC1079F7E95D9EB87DDD87` (git blob `aba9e488124928fba7d18fbb22f6d056b20c8eff`, 402609 bytes, LF, git-object SHA-256 `B051005536E0780E24D2E85C026E45867EC9625851F9D28A319EA389D2F7AC3D`), Checks `BAD35DD0BFFD06A007E5C552C494AAA823AF1B266CB2F74498EF01E0B614DC9D` (git blob `aef903bfaf40998fb168184274973214f62bcee4`, 6581 bytes, LF, git-object SHA-256 `B3CC116C69C80931EF582D394E33D492AD94F5AA7262AF851FE899650D39612F`). Parent Lean blobs `8ebb66f8f643bd3cd74c9c828c6d88aa728b33e9` / `8046170dcdd7f8804864d79ab479de48e5516a78` (391914 / 5899 bytes; SHA-256 `7F1866ED2F508B2909E9D90C323BA5C4259969829ED0214E7967C0B3536367DE` / `278CD6A23C62792B75B62E670E1B44F256FCA45276FF6522CE005E94F465B621`). Cert commit `29a8713` adds evidence only; Lean blobs unchanged from `f7f338b` (`git diff --name-only f7f338b 29a8713 -- '*.lean'` empty; same blob ids). `ActualSelectedCmmsaSeededMap.lean` blob `9fa1a0ed2649fcb3424c62a861abd545f24b0357` identical at parent and freeze (2944 bytes, SHA-256 `A0EFD901492C1D0DDB0012B3CDF545B06C51574812F5AC894257309E0B560786`). `FiniteSourceSampler.lean` / `ExecutablePipelineInput.lean` blobs `7f920ffa` / `f4593745` unchanged (SHA-256 `239DDC6E4FC2171C2882B4D5E753B0306103B6DE20A6635EBAA08B7B12ADD4E1` / `B0C513DD5680D6504EE94D480998DBCCF691F7F132BED993755F4C202364E24C`). This review used only `git cat-file` blobs at `f7f338b`. Windows working-tree Main/Checks hash as CRLF (`411892` / `6761` bytes, SHA-256 `6154025F…` / `44D0FD14…`); LF-normalized bytes match the freeze hashes above. `git status --short` is clean (autocrlf). Evidence `lean/evidence/2026-09-16-actual-decode-input-fp-fresh-run/` local target-fresh PASS naming `f7f338b`; GCP builder reauth failed (`gcp-decode-input-unavailable.txt`). `#print axioms` of `decodeInputTag_mem_FP` / `readInputTag_mem_FP` / `readInputTag_of_tree` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean on the freeze Main blob (`sorry` / `native_decide` / `admit` / `axiom` count 0). No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is a genuine Cobham `FP` membership of the packed decoder tag `decodeInputTag`, via a real field packing `readInputTag` of `ExecutablePipelineInput.readInput` composed with the existing `treeParseTag` and a trailing-bits guard. It is not un-packed semantic `decodeInput ∈ FP` as a named machine class beyond the tag, not `selectedPairedRun_mem_FP`, not `selectedSeededMap`, and not Theorem 1.

## Force

The compiled public theorems are exactly the freeze statements:

```lean
theorem readInputTag_mem_FP : readInputTag ∈ Complexity.FP

theorem readInputTag_of_tree (t : CMMSACodec.Tree) :
    readInputTag (CMMSACodec.Tree.encode t) =
      match ExecutablePipelineInput.readInput t with
      | none => []
      | some x => true :: ExecutablePipelineInput.encodeInput x

theorem decodeInputTag_mem_FP : decodeInputTag ∈ Complexity.FP
```

`decodeInputTag` stays the existing spec-tag

```lean
def decodeInputTag (bs : List Bool) : List Bool :=
  match ExecutablePipelineInput.decodeInput bs with
  | none => []
  | some x => true :: ExecutablePipelineInput.encodeInput x
```

and `decodeInput` is the unchanged parser `Tree.parse (bs.length+1) bs` then `if rest = [] then readInput tree else none`. `FP` here is Complexitylib’s TM class `{f | ∃ d k tm T, tm.ComputesInTime f T ∧ T =O (·^d)}`. Membership is not a custom machine and not a new complexity axiom.

Parent `98ffac0` still had a *private dummy* `readInputTag` that matched `Tree.parse` then semantic `readInput`, plus a *conditional* `decodeInputTag_mem_FP_of_read` needing `readInputTag ∈ FP`. That dummy is deleted. The freeze `readInputTag` is a public total tape function assembled from already-packed field readers:

- shape guards: four nested `splitNode` checks for `.node ws (.node rows (.node q (.node b m)))`, matching `readInput`’s pattern;
- `inputWTag = readListTag ∘ nodeLeft` packs `readList readSigned` on the weights subtree;
- `inputRArg` pairs `listLenBits (dropOne (inputWTag z))` with the rows subtree, so the row arity is the packed weights length, not a constant;
- `inputRTag = readRowListTag ∘ inputRArg` packs `readList (readRow weights.length)`;
- `inputTTag = readTableTag ∘ inputRTag` packs `FiniteSourceSampler.readTable` / `ValidRows` (nonempty, nonnegative, sum = 1) via the parent `readTableTag_of_rows`;
- `inputPTag` / `inputBTag` / `inputMTag` pack `readParameters`, precision `readNat`, and trials `readNat`;
- `inputWrap` rebuilds `true :: encodeInput x` by `wrapInputEnc` of the *canonical* field encodings (`listTree` of `signedTree` / `rowTree`, `parameterTree`, `natTree`). `wrapInputEnc_eq` is the `Tree.encode` layout of `inputTree`, not a slogan.

`readInputTag` is nested `selectHead (emptyFlag ·) []` on those nine probes, then `inputWrap`. Empty field tag = none = `[]`. That is the same Cobham failure convention as the earlier field tags. It is not a dummy constant and not an identity reduction.

`readInputTag_mem_FP` is that algebra: `mem_FP_comp` of `nodeLeft_mem_FP` / `nodeRight_mem_FP` / `splitNode_mem_FP` / `dropOneFn_mem_FP` / `listLenBits_mem_FP` / `pairFn_mem_FP` with the existing `readListTag_mem_FP` / `readRowListTag_mem_FP` / `readTableTag_mem_FP` / `readParametersTag_mem_FP` / `readNatTag_mem_FP`, then `Cobham.selectHeadFn_mem_FP` / `emptyFlagFn_mem_FP` / `constFn_mem_FP []` / `appendFn_mem_FP` / `cons_mem_FP`. No new combinator.

`readInputTag_of_tree` is a real identity chain on complete encodings, not `rfl` of a spec restated as `readInput`:

1. Leaf, or a node missing any of the four nested frames, hits `splitNode_leaf` / `emptyFlag_nil` and packs `[]`, matching `readInput`’s `_ => none`.
2. Successful weights use `readListTag_of_tree`; failure is `[]`. On `some weights`, `dropOne` plus `listLenBits_of_listTree` plus `List.length_map` supplies `weights.length.bits` to `readRowListTag_of_pair`.
3. Successful rows use `readRowListTag_of_pair`; failure is `readTableTag_empty`. On `some rowlist`, `readTableTag_of_rows` is the parent ValidRows identity: nonempty/`vSeen`, nonnegative/sign-fail, sum=`foldAcc`/`mulCanon_bitValue`. `¬ ValidRows` writes `[]` and matches `readTable`.
4. Parameters / precision / trials use `readParametersTag_of_tree` / `readNatTag_of_tree`. The success wrap is `wrapInputEnc_eq` on `⟨weights, ⟨rowlist, hval⟩, params, prec, trials⟩`.

Quantifiers on `of_tree` are honest for every `Tree`, including `.leaf`, missing frames, empty rows (`ValidRows []` is false), and field/`ValidRows` failure. They are not a well-formed-only fragment.

`decodeInputTag_mem_FP` is the existing composition, now instantiated rather than left conditional:

```lean
decodeInputTag bs =
  Cobham.selectHead (emptyFlag (treeParseTag bs)) []
    (Cobham.selectHead (emptyFlag (pairSnd (dropOne (treeParseTag bs))))
      (readInputTag (pairFst (dropOne (treeParseTag bs))))
      [])
```

- parse `none` (empty, truncated `true`, leftover fuel-zero) → `[]` by `emptyFlag` of `treeParseTag`;
- `some (t, rest)` with `rest ≠ []` → `[]` by `emptyFlag` of `pairSnd` (the freeze trailing-bits guard; `decodeInput` requires `rest = []`);
- `some (t, [])` → `readInputTag (encode t)`, rewritten by `readInputTag_of_tree` onto `readInput t`.

`decodeInputTag_mem_FP_of_read` is unchanged combinator algebra: `treeParseTag_mem_FP`, `dropOneFn_mem_FP`, `mem_FP_comp` with `fstBlock_mem_FP` / `sndBlock_mem_FP`, `emptyFlagFn_mem_FP`, `selectHeadFn_mem_FP`, `constFn_mem_FP []`, then `mem_FP_of_eq` onto the spec-tag. The public theorem is `decodeInputTag_mem_FP_of_read readInputTag_mem_FP`. That is spec-equals-impl for a packed composition, not a second function quietly swapped into `FP`.

Together: a total Cobham-`FP` tape function, on every bitstring, outputs `[]` or `true :: encodeInput x` according as `decodeInput` is `none` or `some x`. Do not read un-packed `decodeInput ∈ FP` off this: `FP` is a class of tape functions; the membership is `decodeInputTag ∈ FP`.

No bound here feeds a switching-quality ratio. No 3SAT→`cmmsaPromise` `Preserves`. No `hSrcCmmsa` inhabitation.

## Packaging and theater

Module/commit titles that say “decodeInput packed FP tag” name this composition. Checks header moves `readInputTag` / `readInputTag_mem_FP` / `readInputTag_of_tree` and `decodeInputTag_mem_FP` onto the Cobham/semantic surface via `decodeInputTag_mem_FP_of_read`. That matches the freeze stop-loss after the parent `readTableTag_of_rows`: pack `readInput` from the field readers, then discharge the existing conditional. That is what compiled.

It is **not** un-packed semantic `decodeInput ∈ FP` as a named machine class beyond the tag. `decodeInput` remains the `Option Input` parser in `ExecutablePipelineInput.lean` (blob `f4593745`, unchanged). There is no `decodeInput_mem_FP`.

It is **not** `selectedPairedRun_mem_FP`. `ActualSelectedCmmsaSeededMap.lean` blob `9fa1a0ed` is identical at parent and freeze; its header still omits `selectedPairedRun_mem_FP` because `paddedRun` is not on the Cobham surface.

It is **not** `selectedSeededMap` and **not** Theorem 1. `hSrcCmmsa` / `selectedSeededMap` appear only as explicit non-claims in the module header. No `PromiseNPHard`, no table compiler, no HN/star compilation.

Theater that this increment is *not*:

- Dummy 3SAT→CMMSA map. Absent.
- Parent dummy `readInputTag` matching `Tree.parse`/`readInput` and then “proved” in `FP` by `rfl`. That private matcher is deleted. The freeze function is nested `selectHead`/`emptyFlag` on packed field tags.
- Identity reduction: `decodeInputTag_eq_guard` is parse + trailing-empty + `readInputTag_of_tree`, not `id`.
- Spec restated as a new function already equal to `readInput` with no field walk. Weights list, `listLenBits` arity, row list, `ValidRows`, parameters, precision, and trials are each a prior packed tag.
- A new complexity axiom. Membership uses the existing Cobham combinators named above.

Domain note (the “notes” in the verdict, not a hole in `decodeInputTag_mem_FP`): `readInputTag_of_tree` quantifies over `encode t`, not over arbitrary tapes. Garbage packed trees still map through the total `readInputTag`; that identity is unused by the decoder, which only feeds `encode t` after a successful complete parse. `decodeInputTag_eq_guard` *does* quantify over every `bs`. Empty / truncated / trailing-bits / field-fail / `ValidRows`-fail all pack `[]` and are in the composition.

`set_option maxHeartbeats 4000000` on `readInputTag_of_tree` is proof-kernel fuel for the nested `cases`/`simp` walk. It is not a complexity hypothesis.

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface, including prior field tags, `readInputTag`, `readInputTag_mem_FP`, `readInputTag_of_tree`, `decodeInputTag_mem_FP`. Examples: prior field tags `∈ Complexity.FP`, `readInputTag ∈ Complexity.FP`, `decodeInputTag ∈ Complexity.FP`, leaf encoding `readInputTag (encode leaf) = []` via `readInputTag_of_tree`, `decodeInputTag [] = []`, truncated `decodeInputTag [true] = []` via `decodeInputTag_none`. Axioms: memberships, of-tree/of-pair identities, and `decodeInputTag_mem_FP` the standard trio. No `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Checks header is the honest boundary. Smoke tests are the failure branches (leaf / empty / truncated); there is no Checks roundtrip `decodeInputTag (encodeInput x) = true :: encodeInput x`.

Local target-fresh of frozen `f7f338b` blobs: main×2 exit 0 (olean `773E14769F846688877E9E0857873E8AB3286E4CBA43D3D3161D6A717ECBB8E8`), checks×2 exit 0 (olean `BB977DD6D036454A4C9B5978347A5D345D62F3CA0B816030172A55B57DDF3BC2`), `MATCH_MAIN=True MATCH_CHECKS=True`. Independent source SHA-256 pins match the closeout table. GCP instance start failed on reauth; certification is local-only.

Not un-packed `decodeInput ∈ FP`. Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the packed-decoder half of a future `selectedPairedRun_mem_FP` (`paddedRun` still needs a Cobham packing of the paired executor, then `selectedSeededMap`, then a 3SAT or 3-Lin → `encodeInput` compiler with `Preserves (1/6)`). Do not close the hardness route on this increment. Do not inhabit `hSrcCmmsa` with identity.

Notes: no HIGH false-force in the compiled theorem `decodeInputTag ∈ FP`. The packing is a real field walk already in `FP`: weights/`readListTag`, arity/`listLenBits`, rows/`readRowListTag`, `ValidRows`/`readTableTag_of_rows`, parameters/precision/trials, then parse + trailing-empty. The notes are the documented limits: `readInputTag_of_tree` on complete encodings (garbage tapes not in that quantifier; the decoder composition is still total), Checks smoke-test only failure branches, local-only cert after GCP reauth failure, and leftover hardness packaging toward `selectedPairedRun_mem_FP`. Those limits do not make the packed membership theater.
