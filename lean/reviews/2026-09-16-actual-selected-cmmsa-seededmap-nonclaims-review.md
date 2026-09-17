# Actual selected CMMSA SeededMap surface: non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `38d9ad0df63e42cea9190657f836822892184010`. Gate logs name `38d9ad0`, not `bba6dbb`. Main `ActualSelectedCmmsaSeededMap.lean` SHA-256 `A0EFD901492C1D0DDB0012B3CDF545B06C51574812F5AC894257309E0B560786`. Checks SHA-256 `3F4971152605229124AB5D1EF04D6758FF89589F8B42F4E843CC2138D5A5136C`. Evidence `research/evidence/2026-09-16-actual-selected-cmmsa-seededmap-fresh-run/`. Independently rehashed local sources at `38d9ad0`, certify commit `1d18f76`, `HEAD`, and the working tree match the freeze and the gate. Certification commit `1d18f76` did not change the Lean sources.

Accepted, freeze stop-loss only (`selectedCoinRuler ∈ FP`; `selectedPairedRun` defined; no `run_fp`, no `SeededMap`, no `hSrcCmmsa`):

- `selectedPairedRun L eps` is `paddedRun L eps` on `pairFst` / `pairSnd`. It is a function definition. There is no `selectedPairedRun_mem_FP` and no `paddedRun_mem_FP`.
- `selectedCoinRuler eps` is `List.replicate (coinRuler eps x.length) false`. `selectedCoinRuler_mem_FP` places that length-only ruler in `FP` from Cobham `const_replicate_mem_FP`, `mulLenFn_mem_FP`, `appendFn_mem_FP`, and `coinRuler_quadratic`. It is not `paddedRun ∈ FP`.
- `selectedSeededMap` is not defined. `selectedPipelinePromise`, `threeSat_to_cmmsa_of_compiler`, and `selected_preserves_cmmsa` are absent.
- The module header reports the freeze-permitted blocker: `paddedRun` / `decodeInput` / `Tree.parse` are not on the Cobham FP surface, so the SeededMap stops until `run_fp` exists. `hSrcCmmsa` is not inhabited. There is no dummy 3SAT→CMMSA identity.

The module header denies dummy 3SAT→CMMSA identity, unconditional Theorem 1, Corollary 2, and P vs NP. Checks `#check` / `#print axioms` only `selectedPairedRun`, `selectedCoinRuler`, and `selectedCoinRuler_mem_FP`; prove ruler length equals `coinRuler`; reduce `selectedPairedRun L (1/4) [] = []`; and inhabit `selectedCoinRuler eps ∈ FP`. Checks do **not** `#check` `selectedPairedRun_mem_FP`, `selectedSeededMap`, or `threeSat_to_cmmsa_of_compiler`, and do not inhabit `hSrcCmmsa`. Main does not import `*Checks.lean`. `#print axioms selectedCoinRuler_mem_FP` is `propext`, `Classical.choice`, `Quot.sound` only. Forbidden-scan is clean. README, `INTEGRITY-CLAIMS.md`, `CHANGELOG.md`, and `CITATION.cff` are unchanged by this increment.

Notes, not blocking:

- Module/commit titles that say "actual selected CMMSA SeededMap surface" are catalog labels. They are not a constructed `SeededMap`, not `selectedPairedRun_mem_FP`, not inhabited `hSrcCmmsa`, not unconditional Theorem 1, Corollary 2, publication, or `P` versus `NP`.
- Unused `open`/`import` of `ActualSatToThreeSatSource`, `ActualHeadlineParameters`, and `RandomizedReduction` does not define a 3SAT→CMMSA map and does not inhabit `theorem1_from_threeSat_to_cmmsa`.
- `selectedCoinRuler_mem_FP` is a quadratic length ruler for each fixed `eps`. Do not cite it as `paddedRun ∈ FP` or as `selectedPairedRun_mem_FP`.
- The empty-input example is a runtime identity on `[]`, not an FP theorem on malformed inputs. The freeze requires malformed-input coverage only of `selectedPairedRun_mem_FP`, which was correctly omitted.

Forbidden claims absent. The freeze’s full SeededMap / `hSrcCmmsa` target remains open. Next: Cobham lemmas for `paddedRun` / `decodeInput` / `Tree.parse`, then `selectedPairedRun_mem_FP` and `selectedSeededMap`. Then a 3SAT (or 3-Lin) → `encodeInput` table compiler ∈ FP with `MapReducesVia` into `selectedPipelinePromise`. Do not inhabit `hSrcCmmsa` with identity, do not sorry `run_fp`, and do not skip to Theorem 1.
