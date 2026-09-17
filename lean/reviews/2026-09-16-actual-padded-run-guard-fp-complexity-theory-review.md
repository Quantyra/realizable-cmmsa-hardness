# Actual paddedRunGuardTag FP complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `b8ba7b55b542759d151410667ed56e50f6dcad3e` (`prove actual paddedRunGuard packed FP tag`). Parent `88cee568897b7264ec1510a2c5c7b25c9fd68da9` (decodeInput packed-FP review commit; Lean parent of this module is still `9fa1a0ed` from the selected-ruler freeze). Independently rehashed git blobs of Main `1B3BCB0452CD11DCB9C7B61E97F35FF8807297C0526F92534BF9DD2F3D7E69C9` (git blob `de09577c74a2910aa2b81a360a5b4c3b5272878f`, 14990 bytes, LF, git-object SHA-256 `857647D14BB529A289D8DB31B22BFFBE3607558D7A4B613F5BD8575A3D8454F8`), Checks `94D888D4645D8BD0EB4231F2766F8878030CDC3C585AC06B4F3A0B055E3344A8` (git blob `3f0fdc959eb9b333b79c142f4adc3a5cd3abd8c5`, 1759 bytes, LF, git-object SHA-256 `0750477F98BF0BE1F20A89F03D62B7E2C8EF5FAD69C69AF26D978334CADAC42B`). Parent Lean blobs `9fa1a0ed2649fcb3424c62a861abd545f24b0357` / `dbb7c8fe608f63ba1b66d81bc3f957a20f15781b` (2944 / 1247 bytes; SHA-256 `A0EFD901492C1D0DDB0012B3CDF545B06C51574812F5AC894257309E0B560786` / `3F4971152605229124AB5D1EF04D6758FF89589F8B42F4E843CC2138D5A5136C`). Cert commit `cba404e` adds evidence only; Lean blobs unchanged from `b8ba7b5` (`git diff --name-only b8ba7b5 cba404e -- '*.lean'` empty; same blob ids). `ActualDecodeInputFP.lean` blob `aba9e488124928fba7d18fbb22f6d056b20c8eff` identical at parent, decodeInput freeze `f7f338b`, and this freeze. `ExecutablePipelineInput.lean` / `ExecutableSamplingPolicy.lean` blobs `f4593745` / `0a2583db` unchanged. This review used only `git cat-file` blobs at `b8ba7b5`. Working-tree Main/Checks are byte-identical LF with the freeze hashes above. `git status --porcelain` is clean. Evidence `lean/evidence/2026-09-16-actual-padded-run-guard-fp-fresh-run/` local target-fresh PASS naming `b8ba7b5`; GCP builder started then idle-stopped (`gcp-padded-run-guard-unavailable.txt`). `#print axioms` of `paddedRunGuardTag_mem_FP` / `paddedRunGuardTag_eq` / `paddedRunGuardTag_empty` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean on the freeze Main and Checks blobs (`sorry` / `native_decide` / `admit` / `axiom` count 0). No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is a genuine Cobham `FP` membership of the packed decode + `coinRuler` length guard `paddedRunGuardTag`, via existing `decodeInputTag_mem_FP` and `selectedCoinRuler_mem_FP` composed with `emptyFlag` / `lenEqFlag` / `selectHead`. Success payload is `true :: pair instanceBits coins`; malformed decode or length-mismatch is `[]`. It is not un-packed semantic `paddedRun ∈ FP`, not `selectedPairedRun_mem_FP`, and not Theorem 1.

## Force

The compiled public theorems of this increment are exactly the freeze statements:

```lean
theorem paddedRunGuardTag_mem_FP (eps : Rat) :
    paddedRunGuardTag eps ∈ Complexity.FP

theorem paddedRunGuardTag_eq (eps : Rat) (z : List Bool) :
    paddedRunGuardTag eps z =
      match decodeInput (pairFst z) with
      | none => []
      | some _ =>
        if (pairSnd z).length = coinRuler eps (pairFst z).length then
          true :: pair (pairFst z) (pairSnd z)
        else []

theorem paddedRunGuardTag_empty (eps : Rat) :
    paddedRunGuardTag eps [] = []
```

`paddedRunGuardTag` is the packed tape function

```lean
def paddedRunGuardTag (eps : Rat) (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (instTag z)) []
    (Cobham.selectHead
      (Cobham.lenEqFlag (pairSnd z) (selectedCoinRuler eps (pairFst z)))
      (true :: pair (pairFst z) (pairSnd z))
      [])
```

with `instTag z = decodeInputTag (pairFst z)`. `FP` here is Complexitylib’s TM class `{f | ∃ d k tm T, tm.ComputesInTime f T ∧ T =O (·^d)}`. Membership is not a custom machine and not a new complexity axiom.

That is a real packing of the *decode + `coinRuler` length* conjuncts of `paddedRunOption`:

```lean
def paddedRunOption (L : Nat) (eps : Rat) (instanceBits coins : Bits) : Option Bits := do
  let x ← decodeInput instanceBits
  if x.precision = SamplingGuarantee.precision x.source.rows.length eps ∧
      x.trials = ComputableSampleCount.count x.weights.length (inverseCeil eps) ∧
      coins.length = coinRuler eps instanceBits.length ∧
      x.trials*x.precision ≤ coins.length then
    runOption L instanceBits (coins.take (x.trials*x.precision))
  else none
```

On a paired tape `z`, `pairFst z` is `instanceBits` and `pairSnd z` is `coins`. The freeze tag implements the first bind and the `coins.length = coinRuler eps instanceBits.length` test, and on success re-emits the guarded pair rather than calling `runOption`. Failure is the same Cobham `[]` convention as `decodeInputTag`. It is not a dummy constant and not an identity reduction.

`paddedRunGuardTag_mem_FP` is that algebra, for each fixed `eps`:

- `instTag_mem_FP` is `mem_FP_comp Cobham.fstBlock_mem_FP decodeInputTag_mem_FP`;
- coins tape is `Cobham.sndBlock_mem_FP`;
- ruler tape is `mem_FP_comp Cobham.fstBlock_mem_FP (selectedCoinRuler_mem_FP eps)`;
- length equality is the local `lenEqFlagFn_mem_FP`, which is `andBitFn_mem_FP` of the two `lenLeFlagFn_mem_FP` directions — the same closure as Complexitylib’s Cobham `lenEqFlag_mem`, lifted to `FP` from existing `FPBridge` combinators, not a new axiom;
- success payload is `mem_FP_comp` of `Cobham.pairFn_mem_FP fstBlock_mem_FP sndBlock_mem_FP` with `Cobham.cons_mem_FP true`;
- outer/inner choice is `Cobham.selectHeadFn_mem_FP` on `emptyFlagFn_mem_FP instTag_mem_FP` and on the length flag, against `constFn_mem_FP []`.

No new combinator. `decodeInputTag_mem_FP` is the parent decodeInput freeze (`f7f338b`); `selectedCoinRuler_mem_FP` is the parent ruler freeze (`9fa1a0ed`). Both are used, not restated.

`paddedRunGuardTag_eq` is a real identity chain on every bitstring, not `rfl` of a spec restated as `paddedRunOption`:

1. `decodeInput (pairFst z) = none` → `instTag z = []` → `emptyFlag_nil` → `[]`.
2. `some _` → `emptyFlag_cons` of `true :: encodeInput x`, then `lenEqFlag` against `selectedCoinRuler eps (pairFst z) = replicate (coinRuler eps (pairFst z).length) false`.
3. `lenEqFlag_eq_true_iff` / `lenEqFlag_flag` rewrite that flag to `[true]` iff `|pairSnd z| = coinRuler eps |pairFst z|`, else `[false]`.
4. `selectHead` then writes `true :: pair (pairFst z) (pairSnd z)` or `[]`.

Quantifiers are honest: `∀ eps, ∀ z`. Empty tape is `paddedRunGuardTag_empty` via `decodeInput_empty`. Garbage pairs, truncated instance bits, and coin-length mismatch are in the composition. `eps ≤ 0` still yields a total polynomial function (`inverseCeil = 0` makes the ruler empty; only empty coins pass).

Together: a total Cobham-`FP` tape function, on every bitstring, outputs `[]` or `true :: pair instanceBits coins` according as decode fails or the `coinRuler` length guard fails, versus both succeeding. Do not read un-packed `paddedRun ∈ FP` off this: `FP` is a class of tape functions; the membership is `paddedRunGuardTag eps ∈ FP`.

No bound here feeds a switching-quality ratio. No 3SAT→`cmmsaPromise` `Preserves`. No `hSrcCmmsa` inhabitation.

## Packaging and theater

Module/commit titles that say “paddedRunGuard packed FP tag” name this composition. Checks header moves `paddedRunGuardTag` / `paddedRunGuardTag_mem_FP` / `paddedRunGuardTag_eq` / `paddedRunGuardTag_empty` onto the Cobham/semantic surface and records that `decodeInputTag_mem_FP` is now available. The remaining gap is named as `runOption` / `checkedBits` / `accepted` / output `tree`. That matches the stop-loss after the parent decodeInput packing: pack the decode + length guard, stop before the executor. That is what compiled.

It is **not** un-packed semantic `paddedRun ∈ FP` as a named machine class beyond the tag. `paddedRun` remains `(paddedRunOption …).getD []` in `ExecutableSamplingPolicy.lean` (blob `0a2583db`, unchanged). There is no `paddedRun_mem_FP`.

It is **not** `selectedPairedRun_mem_FP`. `selectedPairedRun` is still the parent Lean wrapper `paddedRun L eps (pairFst z) (pairSnd z)` with no membership theorem. Header still omits it because the remaining `paddedRunOption` conjuncts and `runOption` are not packed.

It is **not** `selectedSeededMap` and **not** Theorem 1. `hSrcCmmsa` / `selectedSeededMap` appear only as explicit non-claims in the module header. No `PromiseNPHard`, no table compiler, no HN/star compilation.

Theater that this increment is *not*:

- Dummy 3SAT→CMMSA map. Absent.
- A spec-matcher `paddedRunGuardTag` defined by matching `paddedRunOption` and then “proved” in `FP` by `rfl`. The freeze function is nested `selectHead` / `emptyFlag` / `lenEqFlag` on packed tags.
- Identity reduction: `paddedRunGuardTag_eq` is decode + length-equality + re-emit of the pair, not `id`.
- Spec restated as a new function already equal to `paddedRun` with no guard walk. Decode is the parent `decodeInputTag`; the ruler is the parent `selectedCoinRuler`; length equality is `lenEqFlag`.
- A new complexity axiom. Membership uses the existing combinators named above. Local `lenEqFlagFn_mem_FP` is `andBitFn_mem_FP` of two `lenLeFlagFn_mem_FP`, not an `axiom`.

Domain note (the “notes” in the verdict, not a hole in `paddedRunGuardTag_mem_FP`): `paddedRunOption` has three further conjuncts after decode + coin length — selected `precision`, selected `trials`, and `x.trials * x.precision ≤ coins.length` — then `runOption`. Those are not in this tag. Success here is the *guarded pair*, not the pipeline output. Private field probes `instEnc` / `weightsEnc` / `rowsEnc` / `paramsEnc` / `precisionEnc` / `trialsEnc` / `weightsLenBits` / `rowsLenBits` (and the copied `splitNode` / `nodeLeft` / `nodeRight` walk of `inputTree`) are compiled with `∈ FP` and of-some identities, but they are unused by `paddedRunGuardTag`. That is leftover scaffolding toward the remaining policy-field guards, not a second function quietly swapped into `FP`, and not a dummy membership of the public theorem.

`inverseCeil eps` remains a *parameter* constant, as in the parent ruler. Polynomial time is in `|z|` for each fixed `eps`.

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface, including prior `selectedCoinRuler_mem_FP` and the new `paddedRunGuardTag` / `paddedRunGuardTag_mem_FP` / `paddedRunGuardTag_eq` / `paddedRunGuardTag_empty`. Examples: `(selectedCoinRuler eps x).length = coinRuler eps x.length`, empty paired run `selectedPairedRun L (1/4) [] = []`, `selectedCoinRuler eps ∈ Complexity.FP`, `paddedRunGuardTag eps ∈ Complexity.FP`, empty-tape `paddedRunGuardTag eps [] = []`. Axioms: memberships and identities the standard trio. No `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Checks header is the honest boundary. Smoke tests are the failure branch (empty tape); there is no Checks roundtrip that a well-formed `encodeInput` paired with a `coinRuler`-length coin tape packs `true :: pair instanceBits coins`.

Local target-fresh of frozen `b8ba7b5` blobs: main×2 exit 0 (olean `85487B040ABB6C47267693905D152392E9F461705078D09FB665F903FCC58F5B`), checks×2 exit 0 (olean `FC2513F4FBD85CC8AEDBD10BA4CB5E53B51034A6C387A912D7DEDEDD0573D5D3`), `MATCH_MAIN=True MATCH_CHECKS=True`. Independent source SHA-256 pins match the closeout table. GCP instance started then immediately stopped; manuscript-repo content-addressed cloud gate is not ported; certification is local-only.

Not un-packed `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the decode + length-guard half of a future `selectedPairedRun_mem_FP` (still needs Cobham packing of the selected precision/trials guards, then `runOption` / `checkedBits` / `accepted` / output `tree`, then `selectedSeededMap`, then a 3SAT or 3-Lin → `encodeInput` compiler with `Preserves (1/6)`). Do not close the hardness route on this increment. Do not inhabit `hSrcCmmsa` with identity.

Notes: no HIGH false-force in the compiled theorem `paddedRunGuardTag eps ∈ FP`. The packing is a real combinator walk already in `FP`: parent `decodeInputTag`, parent `selectedCoinRuler`, `lenEqFlag` of the coin tape against that ruler, `selectHead` onto `true :: pair instanceBits coins` or `[]`. The notes are the documented limits: unused private field-walk scaffolding toward remaining `paddedRunOption` conjuncts, Checks smoke-test only the empty-tape failure, local-only cert after GCP idle-stop, and leftover hardness packaging toward `selectedPairedRun_mem_FP`. Those limits do not make the packed membership theater.
