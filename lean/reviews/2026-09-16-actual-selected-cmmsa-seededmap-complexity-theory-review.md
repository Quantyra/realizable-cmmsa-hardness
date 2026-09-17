# Actual selected CMMSA SeededMap complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `38d9ad0df63e42cea9190657f836822892184010`. Independently rehashed local main `A0EFD901492C1D0DDB0012B3CDF545B06C51574812F5AC894257309E0B560786`, Checks `3F4971152605229124AB5D1EF04D6758FF89589F8B42F4E843CC2138D5A5136C`; objects `1CC96DB9…F3B3` / `E3C01045…BDE8`. Evidence `research/evidence/2026-09-16-actual-selected-cmmsa-seededmap-fresh-run/` gate PASS naming `38d9ad0`. `#print axioms` of `selectedCoinRuler_mem_FP` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean. No leaf-star imports.

This increment is a genuine Cobham `FP` length ruler for the selected sampling coin bound, plus a *defined but uncertified* paired `paddedRun` executor. It is not a `SeededMap`, not 3SAT→`cmmsaPromise` `Preserves`, and not unconditional Theorem 1.

## Force

`selectedCoinRuler eps` is the unary ruler `x ↦ replicate (coinRuler eps |x|) false`. It reads only input length. For each fixed `eps : ℚ` the function is in Complexitylib `FP` by the public Cobham length algebra, not by a custom TM:

- `n²` zeros from `mulLenFn_mem_FP id_mem_FP id_mem_FP`;
- `11n` zeros from `const_replicate_mem_FP 11` and `mulLenFn_mem_FP` against `id`;
- `n² + 11n` by `appendFn_mem_FP`;
- scale `512 · inverseCeil(eps)³` by `const_replicate_mem_FP` of that `Nat` and another `mulLenFn_mem_FP`.

`coinRuler_quadratic` is the identity used: `coinRuler eps n = 512 · inverseCeil eps ^ 3 · (n² + 11n)`. The rewrite `Nat.pow_two` matches `n*n` to `n^2`. Checks prove `(selectedCoinRuler eps x).length = coinRuler eps x.length` for every `eps` and `x`. That is exactly `SeededMap.ruler_length` for `coinCount := coinRuler eps`. Quantifiers are honest: `∀ eps, selectedCoinRuler eps ∈ FP`, including `eps ≤ 0` (then `inverseCeil = 0` and the ruler is the empty tape, still polynomial).

`inverseCeil eps` is a *parameter* constant, not an input-computed function. Polynomial time is in `|x|` for each fixed `eps`. Degree is two. Once a `SeededMap` existed, `coinCount_poly` would follow from `ruler_fp` via `output_length_poly_of_mem_FP`; this module does not assemble that structure.

`selectedPairedRun L eps` is the actual sampling executor: `paddedRun L eps` on `pairFst` / `pairSnd`. It is not identity and not a dummy 3SAT→CMMSA map. It is a Lean function only. There is no `selectedPairedRun_mem_FP`.

## Packaging and theater

Module/commit titles that say “selected CMMSA SeededMap” name the intended consumer. `selectedSeededMap` is **not** defined. `SeededMap` requires `run ∈ FP`; freeze instruction after a genuine Cobham miss is to ship the ruler, define the run, and stop. That is what compiled.

The omitted `run_fp` is a real algebra gap, not a `sorry`. `decodeInput` is `Tree.parse` (fuel-bounded recursive binary tree decoder) then `readInput` (signed rationals, formulas, source tables, rounding parameters, precision, trial count). `paddedRunOption` then guards selected policy fields and `coinRuler` length, and `runOption` calls `ExecutablePipeline.checkedBits` (sample/repair/round/encode). Complexitylib Cobham closes pairing-block `pairFst`/`pairSnd`, `takeLen`, `mulLen`, `append`, `const_replicate`, and `selectHead`. It does not close this `Tree.parse` / `readInput` / arithmetic pipeline. Correctness of `paddedRun` on *selected valid* encodings (`paddedRun_selected_valid`, `padded_executor_good_probability` from the prior policy module) is not `FP`: `FP` is a total function class and must include malformed strings. Checks exercise that convention: `selectedPairedRun L (1/4) [] = []` via `decodeInput_empty`.

`selectedPipelinePromise`, `threeSat_to_cmmsa_of_compiler`, and `selected_preserves_cmmsa` are absent. `hSrcCmmsa` is not inhabited. Imports of `ActualSatToThreeSatSource` and `ActualHeadlineParameters` are unused in the proved theorems (freeze-permitted packaging). They do not smuggle a 3SAT→CMMSA map or specialize `theorem1_from_threeSat_to_cmmsa`. No bound here feeds a switching-quality ratio.

Do not read a randomized reduction off `selectedPairedRun`. Without `run_fp` there is no polynomial coin-using Karp map, no `Preserves (1/6)`, and no composition with `fpSeededMap compile`.

## Checks and non-credits

Checks `#check` `selectedPairedRun`, `selectedCoinRuler`, `selectedCoinRuler_mem_FP` and `#print axioms` of the only public theorem. Length equality against `coinRuler`. Empty paired run. Direct `∈ FP` example. No `#check selectedSeededMap`, no `#check threeSat_to_cmmsa_of_compiler`, no identity 3SAT→CMMSA, no inhabitation of `hSrcCmmsa` or `theorem1_from_threeSat_to_cmmsa`. Axioms standard.

Not a constructed 3SAT→`cmmsaPromise` `Preserves`. Not a table compiler ∈ `FP`. Not HN/star compilation. Not deterministic `PromiseNPHard`. Not credited: unconditional Theorem 1, Corollary 2, P vs NP.

Usable as the length-only quadratic `ruler_fp` half of a future selected sampling `SeededMap`. Next consumer remains Cobham-closing `Tree.parse` / `decodeInput` / `paddedRun` (or an equivalent total FP transducer that agrees on selected encodings and returns `[]` on malformed input), then `selectedPairedRun_mem_FP` and `selectedSeededMap`, then a 3SAT (or 3-Lin) → `encodeInput` compiler with `MapReducesVia` into a decode-mean pipeline promise and a `Preserves (1/6)` lift from `computed_yes_probability` / `computed_no_probability`. Do not close the hardness route on this increment.
