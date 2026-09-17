# Actual readTableTag_of_rows complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `a59171452a27edff5eaf99365fbcf64e402a307f` (`prove actual readTableTag tree agreement`). Parent `1b47db71a587de7bb941f4d6d4acef6746cffb5c` (certified companion of `listLenBits_mem_FP` / `e8eb955`, already carrying packed `readTableTag_mem_FP`). Independently rehashed git blobs of Main `7F1866ED2F508B2909E9D90C323BA5C4259969829ED0214E7967C0B3536367DE` (git blob `8ebb66f8f643bd3cd74c9c828c6d88aa728b33e9`, 391914 bytes, LF, git-object SHA-256 `AD262042E98262E9A48A7AE51506A6985C7CCE9ABF696F311A3948E01BAD2FD3`), Checks `278CD6A23C62792B75B62E670E1B44F256FCA45276FF6522CE005E94F465B621` (git blob `8046170dcdd7f8804864d79ab479de48e5516a78`, 5899 bytes, LF, git-object SHA-256 `A8500DAFE17D9AC1E75EF3CAA9B095A0E4419351B4276D9731970F1BD33E58F1`). Parent Lean blobs `a568f7140a45c00e807d7e461aeaf7f2344ac1b9` / `0c55d6a88175b3b62677423117844584f16e94ed` (347692 / 5545 bytes; SHA-256 `F8E38B60723AE061A03DF57C47B705DA776D31668473B5F9F873A047167A1231` / `6273D91EA46F82C6592BC1010F8FB71798B53CE39416098BB737EE4F7B062836`). Cert commit `f5995f2` adds evidence only; Lean blobs unchanged from `a591714` (`git diff --name-only a591714 HEAD -- '*.lean'` empty). `ActualSelectedCmmsaSeededMap.lean` blob `9fa1a0ed2649fcb3424c62a861abd545f24b0357` identical at parent and freeze (2944 bytes, SHA-256 `A0EFD901492C1D0DDB0012B3CDF545B06C51574812F5AC894257309E0B560786`). `FiniteSourceSampler.lean` / `ExecutablePipelineInput.lean` blobs `7f920ffa` / `f4593745` unchanged (SHA-256 `239DDC6E4FC2171C2882B4D5E753B0306103B6DE20A6635EBAA08B7B12ADD4E1` / `B0C513DD5680D6504EE94D480998DBCCF691F7F132BED993755F4C202364E24C`). This review used only `git cat-file` blobs at `a591714`. Local working-tree Main/Checks are dirty (`git status --short` reports `M` on both; Main 409847 bytes SHA-256 `16F60349…`, Checks 6761 bytes SHA-256 `44D0FD14…`, extra content beyond CRLF) and were not read as source. Evidence `lean/evidence/2026-09-16-actual-read-table-of-rows-fresh-run/` local target-fresh PASS naming `a591714`; GCP builder reauth failed (`gcp-of-rows-unavailable.txt`). `#print axioms` of `readTableTag_of_rows` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean on the freeze Main blob (`sorry` / `native_decide` / `admit` / `axiom` count 0). No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is genuine semantic agreement of the already-packed Cobham tag `readTableTag` with `FiniteSourceSampler.ValidRows` on complete `rowTree` list encodings. It is not `decodeInput ∈ FP` and not Theorem 1.

## Force

The compiled public theorem is exactly the freeze statement:

```lean
theorem readTableTag_of_rows {N : Nat}
    (rows : List (FiniteSourceSampler.Row N)) :
    readTableTag (true :: CMMSACodec.Tree.encode
        (CMMSACodec.listTree (rows.map ExecutablePipelineInput.rowTree))) =
      if FiniteSourceSampler.ValidRows rows then
        true :: CMMSACodec.Tree.encode
          (CMMSACodec.listTree (rows.map ExecutablePipelineInput.rowTree))
      else []
```

`validRowsFlag` stays private. `ValidRows` is the unchanged sampler predicate

```lean
0 < rows.length ∧ (∀ i : Fin rows.length, 0 ≤ (rows.get i).1) ∧
  (∑ i : Fin rows.length, (rows.get i).1) = 1
```

which is exactly `readTable`’s guard. Quantifiers are honest: the identity is for every `List (Row N)`, including `[]`, negative probabilities, and non-unit sums. It is not a well-formed-only fragment and not a dummy constant.

This commit does **not** redefine `readTableTag` / `validRowsFlag` / `validRun` / `validStep`. Those definitions are unchanged from the parent `readTableTag_mem_FP` packing. The new content is an identity chain on that existing transducer:

1. `readTableTag (true :: rowsEnc rows)` reduces to `selectHead (validRowsFlag (rowsEnc rows)) (true :: rowsEnc rows) []` because `emptyFlag` of a nonempty prefix is false and `dropOne` strips the success bit. Empty tape stays `[]` by the old `readTableTag_empty`.
2. `validRowsFlag_of_rows` is the three-conjunct agreement the freeze named, on the packed `validRun` accumulators:
   - **nonempty** is `vSeen`: `validSeen [] = []` and `validSeen (r :: _) = [true]`. Empty list therefore packs `[]`, matching `¬ ValidRows []`.
   - **nonnegative** is the signed-tree walk: `eqFlag (nodeLeft (signedTree q)) [false]` is the nonnegative tag; any `q < 0` writes fail-flag `[true]` and stays (`validStep_cons_neg` / `validRun_neg`). `∀ r ∈ rows, 0 ≤ r.1` is identified with the Fin-indexed conjunct via `forall_rows_nonneg`.
   - **sum = 1** is the common-denominator walk `foldAcc`, init `(0,1)`, step `(num * den_r + num_r * den, den * den_r)`. `foldAcc_ratio_nonneg` plus `foldAcc_eq_one_iff` give `(foldAcc 0 1 rows).1 = (foldAcc 0 1 rows).2 ↔ (rows.map (·.1)).sum = 1` on the nonnegative fragment. `list_sum_eq_fin_sum` restores the Finset sum in `ValidRows`. Packed equality is `eqFlag vNum vDen`, transported by `bits_inj`.
3. The packed step is real arithmetic, not a slogan:
   - `vNBits` / `vDBits` reconstruct `q.num.natAbs.bits` / `q.den.bits` from `readDigitsTag_of_tree` on `ratTree`.
   - `vSucc_cons` rewrites `mulCanon` / `addCanon` through `mulCanon_eq_bits` / `addCanon_eq_bits` (i.e. `mulCanon_bitValue` / `addCanon_bitValue`) onto the `foldAcc` step.
   - Denominator `0` cannot occur on this domain: `Rat.den_pos` plus `bits_eq_nil` rejection in `validDigitsOk_cons`.
4. Length-clamp is discharged, not ornamental. Parent `validClamp` keeps iterate width polynomial. On `rowTree` encodings, `foldAcc_bits_len` / `foldAcc_clamp` prove `|foldAcc.1.bits|` and `|foldAcc.2.bits|` fit in `|validBound enc| = 2|enc|+64`, so `List.take_of_length_le` makes the clamp the identity (`vSucc_cons`). Truncation cannot silently alter the flag on this domain.
5. The ruler is used: `|validRuler enc| = |enc|+1`. `rowsEnc_length_ge` gives `rows.length + 1 ≤ |enc|`, so the iterate splits as extra idle steps after a `rows.length` walk, then `validStep_leaf` on `[false]`. Negative rows fail-flag and stay for the remaining clock.

Together with the parent `readTableTag_mem_FP`, the complexity content is: a total Cobham-`FP` tape function, restricted to the image of `true :: encode (listTree (rows.map rowTree))`, outputs that same packed tape or `[]` according as `ValidRows`. Do not read `readTable ∈ FP` off this: `FP` is a class of tape functions; the membership is `readTableTag ∈ FP`, and this theorem is agreement on encodings.

No bound here feeds a switching-quality ratio. No 3SAT→`cmmsaPromise` `Preserves`. No `hSrcCmmsa` inhabitation.

## Packaging and theater

Module/commit titles that say “readTableTag tree agreement” name this identity. Checks header moves `readTableTag_of_rows` onto the Cobham/semantic surface and keeps `decodeInputTag_mem_FP` as remaining. That matches the freeze stop-loss: if only `readTableTag_of_rows` lands, commit it and do not `sorry` the decoder. That is what compiled (`decodeInputTag_mem_FP` is still only the *conditional* `decodeInputTag_mem_FP_of_read` needing `readInputTag ∈ FP`).

It is **not** `decodeInput ∈ FP`. `decodeInputTag` is still defined by matching semantic `decodeInput`. This commit adds no `readInputTag_mem_FP`. Freeze next-consumers after this theorem are `readInputTag_mem_FP` from the already-packed field readers, then `decodeInputTag_mem_FP`.

It is **not** Theorem 1. `ActualSelectedCmmsaSeededMap.lean` blob `9fa1a0ed` is identical at parent and freeze. `hSrcCmmsa` / `selectedSeededMap` appear only as explicit non-claims in the module header. No `PromiseNPHard`, no table compiler, no HN/star compilation.

Theater that this increment is *not*:

- Dummy 3SAT→CMMSA map. Absent.
- Spec restated as a new function already equal to `ValidRows` and then “proved” by `rfl`. `validRowsFlag` is still `selectHead` on `validRun` accumulators; `validRowsFlag_of_rows` is a walk through sign tags, `foldAcc`, `mulCanon_bitValue`, and `eqFlag`.
- Width-clamp as a silent truncator on the agreement domain. Clamp identity is proved from `Nat.size` bounds of the common-denominator walk.
- Claiming `readTable ∈ FP` or `decodeInput ∈ FP`. Membership theorems are unchanged except the new identity; `readTableTag_mem_FP` is the parent packing.

Domain note (the “notes” in the verdict, not a hole in the theorem): agreement is on `true :: encode (listTree (rows.map rowTree))`, not on arbitrary tapes. Garbage packed rows still map through the total parent tag; this theorem does not quantify over them. Empty list → `[]` is in the theorem (`ValidRows []` is false). Formula subtrees are not re-checked because `ValidRows` / `readTable` do not mention formulas; the rows are already typed `Row N`.

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface, including `readTableTag`, `readTableTag_mem_FP`, `readTableTag_empty`, `readTableTag_of_rows`. Examples: prior field tags `∈ Complexity.FP`, `readTableTag [] = []`, and the empty-row encoding via `readTableTag_of_rows []` (the invalid/`[]` branch). Axioms: memberships, of-tree/of-pair identities, decode packing lemmas, and `readTableTag_of_rows` the standard trio. No `#check decodeInputTag_mem_FP`, no `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Checks header is the honest boundary.

Local target-fresh of frozen `a591714` blobs: main×2 exit 0 (olean `05288D3D0DDA3EFD6300642D10CE2774D4B77551DAFD010014D23880F97BEFE5`), checks×2 exit 0 (olean `E615ED35D700F69C6C417E08391140702D4B6F0EDAD5B7B5B055A093D29F14E0`), `MATCH_MAIN=True MATCH_CHECKS=True`. Independent source SHA-256 pins match the closeout table. GCP instance start failed on reauth; certification is local-only. Current `.lake/build` oleans were not used (dirty Luna worktree).

Not `decodeInput ∈ FP`. Not `readTable ∈ FP`. Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `decodeInputTag_mem_FP`, `readInputTag_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the packed-table semantic half of a future `decodeInputTag_mem_FP` (`readInputTag_mem_FP` from `readListTag` / `readRowListTag` / `readTableTag` / `readParametersTag` / `readNatTag` / `listLenBits`, then the existing `decodeInputTag_mem_FP_of_read`). Next consumer remains that decoder, then `selectedPairedRun_mem_FP` / `selectedSeededMap`, then a 3SAT (or 3-Lin) → `encodeInput` compiler with `Preserves (1/6)`. Do not close the hardness route on this increment.

Notes: no HIGH false-force in the compiled theorem `readTableTag_of_rows`. The identity is real ValidRows agreement of the same packed function already in `FP`: nonempty/`vSeen`, nonnegative/sign-fail, sum=`foldAcc`/`mulCanon_bitValue`. The notes are the documented limits: complete `rowTree`-list domain (garbage tapes not in the quantifier), Checks smoke-test only the empty/invalid branch, local-only cert after GCP reauth failure, and leftover module packaging toward `decodeInputTag ∈ FP`. Those limits do not make the agreement theater.
