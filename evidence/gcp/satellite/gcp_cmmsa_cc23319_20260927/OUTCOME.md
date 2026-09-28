# GCP exact-source Lean build and replay

Run: 2026-09-28 UTC / 2026-09-27 Pacific
Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`
Source commit: `cc23319a413f8e250a63666c577e759ed79d1e36`
Scope: `ActualCnfQueryStar`, `ActualCnfQueryStarChecks`, `ActualPredrawRepresentativeAcceptance`, and `ActualPredrawRepresentativeAcceptanceChecks`.

The VM could not reach GitHub, so the input was `git archive` of the committed `lean/`, `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`. The input archive SHA-256 was `746c3b46db787a10eff5e6a488ba4c7d1ba1068782cad86ae6e2e6eb4b9dda0b`. The VM verified that hash before extraction and verified the four touched file hashes in `source.sha256` before the build and after the replay. The input archive remains local; the committed Lean source is at the pinned commit.

Lean 4.34.0-rc2 / Lake 5.0.0 built all four targets in a fresh extracted source tree: **3,460 jobs, exit 0**. The checks were run with `lake env lean`, including axiom prints. The local `.lake/build` was removed, and a clean replay rebuilt the same four targets: **3,460 jobs, exit 0**. Both build logs have no `error:` lines. The new checked theorems report only `propext`, `Classical.choice`, and `Quot.sound`. The changed source introduces no `sorry`, `admit`, `native_decide`, or axiom declaration.

Remote run outcome: `EXIT=0`, ending `2026-09-28T05:25:54Z`. The hidden local collector downloaded the sealed evidence archive, then stopped the builder; `stop` exited 0 and the final instance state was **TERMINATED**. Sealed evidence SHA-256: `6a3b1734cffc99e549fdb20f5c1cfe7f3aabb116811bff61f6e12f39ce409666`. Extracted logs and source-hash reports are beside this note.

This certifies only the bounded modules above. It does not prove positive physical acceptance, a source-dependent star score bound, the encoded reduction, manuscript Theorem 1, or Corollary 2.
