# Actual Theorem 1 (conditional two-stage Preserves): non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `10c3b9b9653852f56e300fc2b8cc202ece2dbf71`. Gate logs name `10c3b9b`, not `bba6dbb`. Main `ActualTheorem1.lean` SHA-256 `C62AAE87A1A4319198D648A431206750C3F48F8562590DAB56DDBA962678ABAF`. Checks SHA-256 `CE241ECFC419AC0D93E7A703B7980BBE92BFDD4613F6EDB6452A1E5524FF2029`. Evidence `research/evidence/2026-09-16-actual-theorem1-fresh-run/`. Independently rehashed local sources at `10c3b9b`, certify commit `024bf2f`, `HEAD`, and the working tree match the freeze and the gate. Certification commit `024bf2f` did not change the Lean sources.

Accepted, Cook–Levin zero-coin lift and hypothesized two-stage packaging only:

- `fpSeededMap f hf` is the zero-coin `SeededMap` with `run = f ∘ pairFst`, empty ruler, and `coinCount = 0`. `fpSeededMap_apply` / `fpSeededMap_coinCount` are that runtime and coin count. `fpSeededMap_preserves` is `Preserves … 0 0` from a deterministic `MapReducesVia`.
- `np_to_sat_seeded` packages Cook–Levin `SAT.NPHard_language` (`A ∈ NP → A ≤ₚ SAT.language`) as a zero-coin `Preserves` from `ofLanguage A` to `ofLanguage SAT.language` at error `0`. It is not a `1/6` map and is not a SAT-to-`cmmsaPromise` map.
- `theorem1_realizable_cmmsa` inhabits `RandomizedPromiseNPHard (cmmsaPromise L sig gam …)` **only from** hypothesized `hSatSrc : Preserves SAT.language → source (1/6)` and `hSrcCmmsa : Preserves source → cmmsaPromise (1/6)`. Cook–Levin is composed at error `0` via `exists_preserving_composition` (`0+1/6=1/6`), then `two_stage_randomized_map` (`1/6+1/6=1/3`). It does not lift Cook–Levin from `0` to `1/6`.
- `L`, `sig`, and `gam` remain parameters under `1 ≤ sig`, `0 < gam < 1`. Manuscript `σ_L` / `γ_L` are not chosen.

The module header denies constructing those `1/6` maps, picking manuscript `σ_L`/`γ_L`, and proving unconditional Theorem 1, Corollary 2, or P vs NP. Checks `#check` / `#print axioms` the public theorems, run `fpSeededMap id` on `[]` and a nonempty list, and inhabit `np_to_sat_seeded` on `SAT.language` only (via `language_mem_NP` and `NPComplete_language.1`). Checks do **not** inhabit `theorem1_realizable_cmmsa`, including not using identity as `hSrcCmmsa`. Main does not import `*Checks.lean`. `#print axioms` of every public theorem is `propext`, `Classical.choice`, `Quot.sound` only. Forbidden-scan is clean.

Notes, not blocking:

- Module/commit titles that say "Actual Theorem 1" / "prove actual theorem1" are catalog labels. They are not unconditional manuscript Theorem 1, Corollary 2, constructed `1/6` maps, publication, or `P` versus `NP`. The freeze doc comment "Manuscript Theorem 1, from SAT-to-source and source-to-CMMSA Preserves (1/6)" is the permitted conditional packaging statement, not a discharged manuscript theorem.
- `np_to_sat_seeded` on `SAT.language` is a 0-error SAT-to-SAT Cook–Levin self-map. It is not a SAT-to-source `Preserves (1/6)` and does not inhabit `RandomizedPromiseNPHard (cmmsaPromise …)`.
- `fpSeededMap id` is a zero-coin identity on bitstrings, not a SAT-to-source or source-to-`cmmsaPromise` `SeededMap`.
- `two_stage_randomized_map` still drops the clock/coin witnesses retained on `two_stage_seededMap` / `exists_preserving_composition`.

Forbidden claims absent. Unconditional manuscript Theorem 1 remains open. Next: construct the two `1/6` maps (SAT-to-regularized-3-Lin source, then source-to-encoded CMMSA). Then Corollary 2 from an inhabited Theorem 1 plus HN parameters. Do not skip those maps.
