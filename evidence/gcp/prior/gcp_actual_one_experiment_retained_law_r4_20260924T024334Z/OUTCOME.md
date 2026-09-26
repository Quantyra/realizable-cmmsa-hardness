# GCP ActualOneExperimentRetainedLaw r4 compilation

- Result: FAIL at direct main build; no repair attempted.
- Accepted Git SHA: `6b522880de618597c5ec427f3dd13fd83665b76e`
- Checkout: fresh detached GCP worktree at `/tmp/gcp-actual-one-experiment-retained-law-r4-20260924T024334Z/checkout`
- Bundle SHA-256: `59e98fa41f22a8d0e3cd96387aeb17a656fbfcfd7fe548f90a63f7b2e941fcda`
- Main frozen SHA-256: `6d9b509336d3a6593cf24a738092b1860deb2af697cbe416c3613857198595cd`
- Checks frozen SHA-256: `02211843a37230d7f289443904a173fc40d3ec260f4914461ae744429d3951c0`
- Lean: `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`
- Lake: `5.0.0-src+6a10ac8`
- Invocation: `~/.elan/bin/lake --old`
- Lean source edits by orchestrator: none
- Local Lean/Lake execution: none
- Git commit or push: none

## Build result

`~/.elan/bin/lake --old build PvNP.RealizableHardness.ActualOneExperimentRetainedLaw` exited `1`.

The first precise diagnostics are:

```text
lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:102:4: Type mismatch: After simplification, term
  hcount
has type
  Nat.card { L // ↑Q0 ≤ ↑L ∧ ↑L ≤ P0.W } =
    gaussian (Module.finrank (ZMod 2) { x : ↥(TripleRestrictionRank.retained s) // x ∈ P0.W } - a) (d - a)
but is expected to have type
  Nat.card
      (Zoom (restrictGrass (TripleRestrictionRank.retained s) Q hQV)
        (localDecodedPair (TripleRestrictionRank.retained s) Q (ambientPair s Q W hQV hQW) hQV ⋯)) =
    gaussian
      (Module.finrank (ZMod 2) { x : TripleRestrictionRank.Vector J // x ∈ TripleRestrictionRank.retained s ⊓ W } - a)
      (d - a)

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:149:6: Type mismatch: After simplification, term
  retainedConditional_uniform s Q L hQV had hd
has type
  ConditionedCovering.retainedConditional s Q L =
    (if ↑Q ≤ ↑L then 1 else 0) / ↑(gaussian (Module.finrank (ZMod 2) ↥(TripleRestrictionRank.retained s) - a) (d - a))
but is expected to have type
  ConditionedCovering.retainedConditional s Q L =
    (↑(gaussian (Module.finrank (ZMod 2) ↥(TripleRestrictionRank.retained s) - a) (d - a)))⁻¹

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:156:13: failed to synthesize instance of type class
  Min Type
```

Further errors occur at lines `160`, `178`, `196`, `204`, `208`, and `219`. The complete 2,031-line output is in `evidence/06-direct-main.log`; extracted context is in `evidence/first-actionable-diagnostics.log`.

Per the stop-on-first-failure policy, Checks, forced combined build, independent replay, OLEAN stability comparison, signature extraction, axiom reports, forbidden-shortcut scan, and anchored-error scan were not run.

## Isolation

The bundle was verified and fetched as exactly `6b522880de618597c5ec427f3dd13fd83665b76e`. The worktree was detached, linked `.lake/packages` and `.lake/build` to `/home/dfredriksen_quantyra_org/mz24-fixed-rho-de048da`, and installed only the frozen target pair. `evidence/05-installed-verification.log` records both installed hashes.

The shared local main changed after remote staging and had SHA-256 `3375007d78f26621e2191602b3e369610b51c83a88b9dc0d56859ffe13ef96c4` after the run. It was not edited or reverted by the orchestrator and did not affect the frozen remote input.

An earlier R4 orchestration attempt at `gcp_actual_one_experiment_retained_law_r4_20260924T023656Z` was invalidated when an ambiguous IAP disconnect caused a second launch to overwrite its outcome with `nonfresh_worktree_path`. It is preserved as transport evidence and is not the compilation receipt reported here.

## VM lifecycle

- Project: `quantyra-lean-cert-20260915`
- Zone: `us-central1-a`
- VM: `quantyra-lean-builder-01`
- Final independently verified state: `TERMINATED`

This is a compilation receipt only and makes no certification claim.
