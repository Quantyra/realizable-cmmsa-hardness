# Actual CMMSA randomized-reduction interface: non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `c0583486d30e65fa3c672a21b163be6f5c1c5b0e`. Gate logs name `c058348`, not `bba6dbb`. Main `ActualCMMSARandomizedReduction.lean` SHA-256 `9CDDC139FCF64A07A4E759AD8F5AA78337123FB0EA131E77924421FC4F776283`. Checks SHA-256 `BF1C7E8BAA430A75CDC94F6E5DE8A68406000C8E23CE0D4955B18546B7390850`. Evidence `research/evidence/2026-09-16-actual-cmmsa-randomized-reduction-fresh-run/`. Independently rehashed local sources at `c058348`, certify commit `c01f6e3`, `HEAD`, and the working tree match the freeze and the gate. Certification commit `c01f6e3` did not change the Lean sources.

Accepted, interface and composition only:

- `cmmsaPromise L sig gam` is the encoded Gap-CMMSA promise: YES is `decode` plus `CMMSACodec.Yes 0`; NO is `decode` plus `CMMSACodec.No sig gam`. `disjoint` is proved from decode uniqueness (`some` injectivity) and `Yes 0` versus `No` under `1 ≤ sig` and `gam < 1`. It is not stored as a hypothesis.
- `cmmsaPromise_yes_of_encode` / `cmmsaPromise_no_of_encode` place `encode i` in the corresponding instance set via `decode_encode`.
- `RandomizedMapReduces source target` is `∃ R : SeededMap, Preserves R source target (1/3) (1/3)`.
- `RandomizedPromiseNPHard target` is the predicate `∀ A, A ∈ NP → RandomizedMapReduces (ofLanguage A) target`. It is defined, `#check`ed, and not instantiated on `cmmsaPromise`.
- `two_stage_seededMap` is `exists_preserving_composition` at `1/6+1/6=1/3`, with polynomial coins and the original-input-length TM clock retained.
- `two_stage_randomized_map` packages that composition as `RandomizedMapReduces`.
- `identitySeededMap` is the zero-coin `pairFst` map. `identitySeededMap_preserves` is 0-error self-preservation; `identitySeededMap_coinCount` is `0`.
- `preserves_mono` lifts smaller error bounds to larger ones. Checks use it to instantiate `two_stage_randomized_map` on identity of `cmmsaPromise 1 1 (1/2)`, as the freeze permits.

The only source doc comments deny `RandomizedPromiseNPHard (cmmsaPromise ...)`, SAT-to-source or source-to-CMMSA `Preserves`, and a P-versus-NP theorem. Checks repeat that no NP-hardness or P-versus-NP theorem is asserted. Main does not import `*Checks.lean`. `#print axioms` of every public theorem is `propext`, `Classical.choice`, `Quot.sound` only. Forbidden-scan is clean.

Notes, not blocking:

- Module/commit titles that say "CMMSA randomized-reduction interface" are catalog labels. They are not Theorem 1, Corollary 2, `RandomizedPromiseNPHard (cmmsaPromise ...)`, SAT-to-CMMSA `Preserves`, publication, or `P` versus `NP`.
- Checks `RandomizedMapReduces samplePromise samplePromise` is identity composed with itself after monotonicity. That is a 0-coin self-map of the encoded promise, not a SAT-to-CMMSA reduction and not NP-hardness of Gap CMMSA.
- `identitySeededMap` is a runtime/asymptotics baseline, not a SAT-to-source or source-to-CMMSA `SeededMap`.
- `two_stage_randomized_map` drops the clock/coin witnesses; those remain on `two_stage_seededMap`.
- Concrete `Instance 1` is used for decode/empty/identity checks. Checks do not exhibit `Yes 0` or `No` on that fixture; the freeze does not require it.

Forbidden claims absent. Manuscript theorem incomplete. Next: an actual SAT-to-source `SeededMap` with `Preserves (1/6) (1/6)`, then source-to-`cmmsaPromise`. Do not skip to Theorem 1.
