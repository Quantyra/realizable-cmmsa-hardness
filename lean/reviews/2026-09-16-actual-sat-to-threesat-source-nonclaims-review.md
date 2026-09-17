# Actual SAT → 3SAT source SeededMap: non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `1488ff84c6d1daad1c1174aa469aeeddedc360aa`. Gate logs name `1488ff8`, not `bba6dbb`. Main `ActualSatToThreeSatSource.lean` SHA-256 `5ADF857840ED4242C184AE248BCFC90703E8D1F250776A975C67B0A6E1A988E4`. Checks SHA-256 `16E3EF2C31E2BF2B1BDFE16D5C324793BBDC9553631FA22E9C7683CB4143B8E9`. Evidence `research/evidence/2026-09-16-actual-sat-to-threesat-source-fresh-run/`. Independently rehashed local sources at `1488ff8`, certify commit `b871a23`, `HEAD`, and the working tree match the freeze and the gate. Certification commit `b871a23` did not change the Lean sources.

Accepted, SAT → encoded-3SAT Karp packaging as a zero-coin then `1/6` `SeededMap` only:

- `threeSatSource` is `PromiseProblem.ofLanguage ThreeSAT.language`. That language is encodings of satisfiable exact-width-three CNFs. It is not regularized 3-Lin and is not `cmmsaPromise`.
- `satToThreeSatMap` is `fpSeededMap ThreeSAT.reduction reduction_mem_FP`. `satToThreeSatMap_apply` is the seed-ignoring runtime `apply x seed = reduction x`. The Karp map is complexitylib `CNF.to3Aux` with a fixed no-instance fallback on malformed encodings, not an identity and not a dummy 3SAT-to-CMMSA map.
- `satToThreeSat_mapReducesVia` is `z ∈ SAT.language ↔ reduction z ∈ ThreeSAT.language`, from `mem_language_iff_reduction_mem`. `CNFSAT.language` is an abbrev of `SAT.language` (`language_eq_sat`, `rfl`), so the source language is honestly SAT, not a renamed third language.
- `satToThreeSat_preserves_zero` is `fpSeededMap_preserves` at error `0`. `satToThreeSat_preserves` is `preserves_mono` from `0 ≤ 1/6`. `satToThreeSat_exists` inhabits that `1/6` existence with `satToThreeSatMap`.
- `theorem1_from_threeSat_to_cmmsa` is `theorem1_headline` with `source = threeSatSource` and `hSatSrc = satToThreeSat_exists`. It still requires `1 ≤ sigmaL L`, `0 < gammaL L < 1`, and hypothesized `hSrcCmmsa : Preserves threeSatSource → cmmsaPromise (1/6)`. It does not inhabit `hSrcCmmsa`.

The module header denies constructing regularized 3-Lin, inhabiting 3SAT → `cmmsaPromise`, and proving unconditional Theorem 1, Corollary 2, or P vs NP. Checks `#check` / `#print axioms` every public theorem, run `satToThreeSatMap.apply` on `[]`, and inhabit `mapReducesVia` / `Preserves 0` / `Preserves (1/6)` / `satToThreeSat_exists` only. Checks do **not** inhabit `theorem1_from_threeSat_to_cmmsa`, including not using identity as `hSrcCmmsa`. Main does not import `*Checks.lean`. `#print axioms` of every public theorem is `propext`, `Classical.choice`, `Quot.sound` only. Forbidden-scan is clean. README, `INTEGRITY-CLAIMS.md`, `CHANGELOG.md`, and `CITATION.cff` are unchanged by this increment.

Notes, not blocking:

- Module/commit titles that say "actual SAT-to-3SAT source" / "prove actual SAT-to-3SAT source SeededMap" are catalog labels. They are not the manuscript SAT → regularized 3-Lin source, unconditional Theorem 1, Corollary 2 NP-hardness, publication, or `P` versus `NP`. The freeze’s “proved SAT → encoded-3SAT Karp reduction as a zero-coin then `1/6` `SeededMap`” is the permitted packaging statement.
- `Preserves (1/6)` is monotonicity from a deterministic 0-error Karp map. It does not introduce coins, sampling, or a new randomized construction. Do not cite it as a coin-using SAT-to-source reduction.
- The Karp correctness and `reduction ∈ FP` facts are imported from complexitylib and locally packaged. This increment does not re-prove SAT-completeness of 3SAT.
- `theorem1_from_threeSat_to_cmmsa` remains a conditional specialization. Inhabiting it would still require a real 3SAT (or regularized 3-Lin) → encoded `cmmsaPromise` `Preserves (1/6)` map. Do not treat the remaining hypothesis as discharged.

Forbidden claims absent. Unconditional Theorem 1, Corollary 2 NP-hardness, regularized 3-Lin, dummy 3SAT-to-CMMSA, P vs NP, and publication remain out of scope. Next: construct 3SAT (or regularized 3-Lin) → encoded `cmmsaPromise` `Preserves (1/6)`. Do not inhabit `hSrcCmmsa` with identity, and do not skip that map.
