# Actual gcdBits FP complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `7105c9504c55226b4143624a4f0143379e11c1ba` (`prove actual gcdBits packed FP tag`). Independently rehashed git blobs of local Main `8C9B46562B478EB93870249071E8636FFEC80A6F8A068E681D2467E0963FBD8A` (git blob `7fff1264a3d6de0eb5bb5857ea4f638222992a27`, 75230 bytes), Checks `3FF960978E4C1567E74B764704612B72044A76639DA2D18EFAC0EF92921422E6` (git blob `bf6d15592bbe352aadd5f94971dc322bf699baa5`, 1108 bytes); objects `68D4E315CDC58A7410C0A5BB1C07ED5675F268040A26121BC735F24C52B749AD` / `4B90D9D4541098CE91846ECD6BA6945FB57A3122F28CF9F106593D01473315C8`. Cert commit `7ccc144` adds evidence only; Lean blobs unchanged from `7105c95` (same blob ids; `git diff --name-only 7105c95 7ccc144 -- '*.lean'` empty). Evidence `research/evidence/2026-09-16-actual-gcd-bits-fp-fresh-run/` gate PASS naming `7105c95`. `#print axioms` of `gcdBits_mem_FP` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean. No leaf-star imports. I made no Lean-source or Git changes and ran no additional broad build.

This increment is a genuine Cobham `FP` membership of a *total* packed Stein-shaped iterate `pairFst ∘ gcdStep^[|gcdRuler|]`, with polynomial width discharged from canonical subtractive length. It is not `readRat ∈ FP`, not `decodeInput ∈ FP`, not NP-hardness, and not Theorem 1.

## Force

`gcdBits : List Bool → List Bool` is the freeze packing of a binary-tape GCD *step iterate*, not a separately defined number-theoretic GCD:

- input tape `z` is the live state (init = `id`);
- `gcdStep` is one subtractive/compare/strip-twos step on `pairFst` / `pairSnd`;
- after `|gcdRuler z| = 2|z|+16` steps, `gcdBits z = pairFst` of that state.

`FP` here is Complexitylib’s TM class `{f | ∃ d k tm T, tm.ComputesInTime f T ∧ T =O (·^d)}`. Membership is not a custom machine. The witness is public `Cobham.iterate_mem_FP gcdStep_mem_FP id_mem_FP gcdRuler_mem_FP gcdWidth_mem_FP hbound`, then `mem_FP_comp` with `fstBlock_mem_FP`. That is exactly the combinator’s conclusion `(fun z => F^[(ruler z).length] (init z)) ∈ FP`.

The one-step machine is real arithmetic, not a dummy tag:

- `subCanon` is two’s-complement subtract on a common pad `wide a b = a ++ b ++ [false]`, then `stripTrailing`.
- `subCanon_bitValue` (hypothesis `bitValue b ≤ bitValue a`) is the identity `bitValue (subCanon a b) = bitValue a - bitValue b`. It is used, not ornamental: `subCanon_length_of_le` rewrites the tape to `(a-b).bits` and bounds `Nat.size(a-b) ≤ Nat.size a ≤ |a|` from `bitValue_lt_two_pow`.
- That is the freeze blocker. Naive `subCanon_length` is `|a|+|b|+1`, which is not closed under iteration. Canonical length `|subCanon a b| ≤ |a|` on the minuend side *is* closed. `dropTwos` is non-increasing (`drop2Step` drops an LSB `false` or stays).
- `gcdStep` is assembled from `emptyFlag`, `eqFlag`, `ltCanon`, `subCanon`, `dropTwos`, `pair`, and `selectHead` — all public Cobham closures. `gcdStep_mem_FP` is that algebra, not a TM.

Iteration parameters are polynomial and used:

- Ruler `gcdRuler z = z ++ z ++ replicate 16 false` has length `2|z|+16`. It is a live clock for `iterate_mem_FP`, not a stuckness theorem.
- Width `gcdWidth z` has length `(2|z|+16)^2` via `mulLenFn_mem_FP`. `GcdReach` keeps `|pairFst st| ≤ |z|` and `|pairSnd st| ≤ |z|`; pairing then fits in `3|z|+2 ≤ (2n+16)^2` (`gcd_sq_bound`). `hbound` is exactly `iterate_mem_FP`’s hypothesis: every prefix of the init trajectory has length `≤ |width z|`.
- `gcdReach_step` invokes `subCanon_length_of_le` on the compared branch (`ltCanon_true_iff` supplies `bitValue` order). Empty / equal branches stay, so the invariant is preserved on garbage as well as on well-formed pairs.

Quantifiers are honest: `gcdBits ∈ FP` is a total function fact, including malformed pair encodings. `id_mem_FP` is the Cobham init and the stay-put `selectHead` branch, not a dummy 3SAT→CMMSA map.

## Packaging and theater

Module/commit titles that say “gcdBits packed FP tag” name this iterate. `gcdBits` is *defined* as `pairFst (gcdStep^[|gcdRuler|] z)`, then proved in `FP`. That is spec-equals-impl for the iterate, not a second function quietly in `FP`. `gcdStep` does not call `Nat.gcd`.

There is no `gcdBits_eq` / stuckness / `eval`-agreement theorem. The ruler `2n+16` is not proved to reach a Stein fixed point. Subtractive Euclid on n-bit Fibonacci is Θ(n) steps and is likely covered by `2|z|+16` on a well-formed pair, but that is not in the kernel. Do not read `Nat.gcd ∈ FP` off `gcdBits_mem_FP`.

The step itself is subtractive Euclid plus `dropTwos` on the *difference* only. It is not classical Stein: common factors of two are not extracted and are not multiplied back. `dropTwos` on `a-b` can drop 2s that belong in `gcd(a,b)` when both arguments are even. Empty `pairFst` stays, so `gcdBits` of `pair [] b` is `[]` rather than `b = gcd(0,b)`. Those are semantic obligations for `readRatTag`, not holes in the `FP` membership.

Module header still says packed `decodeInput` as a total function in `FP`. The compiled public membership is `gcdBits_mem_FP`. `decodeInputTag` is defined, and `decodeInputTag_mem_FP_of_read` is a *conditional* lemma needing `readInputTag ∈ FP`, which is not proved. Checks comment correctly: `readRatTag_mem_FP` / `decodeInputTag_mem_FP` remain.

`readRatTag_mem_FP`, `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, and `selectedSeededMap` are absent as theorems. Freeze stop-loss after a genuine `gcdBits_mem_FP`-only success is to stop and not `sorry` the consumers. That is what compiled. `ActualSelectedCmmsaSeededMap.lean` is untouched (`38d9ad0`).

`hSrcCmmsa` is not inhabited. No 3SAT→`cmmsaPromise` `Preserves`, no table compiler, no HN/star compilation. No bound here feeds a switching-quality ratio. Do not read a randomized reduction, `PromiseNPHard`, or unconditional Theorem 1 off this membership.

The quadratic width `(2n+16)^2` is pairing/measure slack, not a claim of quadratic-time TM complexity. `iterate_mem_FP` supplies some polynomial; degree is not computed here and is not needed for `∈ FP`.

Windows working-tree Main hashes as CRLF (`77029` bytes, SHA-256 `E3290432…`); the git blob and the Linux certification checkout are LF `75230` bytes matching `8C9B4656…`. Not source drift.

## Checks and non-credits

Checks `#check` / `#print axioms` of the public surface: `decodeInputTag`, `decodeInputTag_empty`, `decodeInputTag_none`, `decodeInputTag_some`, `gcdBits`, `gcdBits_mem_FP`. Examples: `gcdBits ∈ Complexity.FP`, `decodeInputTag [] = []`, truncated `decodeInputTag [true] = []` via `decodeInputTag_none`. Axioms: membership and the decode packing lemmas the standard trio. No `#check readRatTag_mem_FP`, no `#check decodeInputTag_mem_FP`, no `#check selectedPairedRun_mem_FP`, no `#check selectedSeededMap`, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`.

Fresh-run stages exception-repair / formula / codec / randomized-reduction / assembly / tree-parse / main×2 / checks×2 all exit 0 (26 rows in `stage-exits.tsv`). Independent rehash PASS, 175 rows, 0 mismatches. Source SHA-256 pins match the blobs above before and after every stage. Bundle SHA-256 `D706ABC78AC3B786CF47FE1DF4FBB4DEDE73B9796F20BC39B5B377C47D9AD756`.

Not `readRat ∈ FP`. Not `decodeInput ∈ FP`. Not `paddedRun ∈ FP`. Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not NP-hardness. Not credited: `readRatTag_mem_FP`, `decodeInputTag_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the packed `gcdStep` iterate half of a future `readRatTag_mem_FP` (semantic GCD of this iterate, or a corrected Stein step, then reduced `ratTree`; `[]` on malformed / den=0). Next consumer remains that rational tag, then `decodeInputTag_mem_FP`, then `selectedPairedRun_mem_FP` / `selectedSeededMap`, then a 3SAT (or 3-Lin) → `encodeInput` compiler with `Preserves (1/6)`. Do not close the hardness route on this increment.

Notes: no HIGH false-force in the compiled theorem `gcdBits ∈ FP`. The notes are the documented limits: no GCD-identity/stuckness theorem, `2n+16` is a polynomial clock not a termination proof, `gcdStep` is not classical Stein, and the module header’s decodeInput-in-FP sentence is leftover packaging. Those limits do not make the iterate membership theater.
