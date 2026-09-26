# GCP ActualOneExperimentRetainedLaw r3 compilation

- Result: FAIL at direct main build; no repair attempted.
- Accepted Git SHA: `6b522880de618597c5ec427f3dd13fd83665b76e`
- Checkout: fresh detached GCP worktree at `/tmp/gcp-actual-one-experiment-retained-law-r3-20260924T022543Z/checkout`
- Bundle SHA-256: `d737a137f50e354bc5e7d02aa00dd75c67bbb78802e1880fd1a0923f0b0c9eee`
- Main frozen SHA-256: `42acbe52a48755e085f46cd61254c3755747a14ab1de0ef76c1ab34229d84b61`
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
lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:62:8:
failed to synthesize instance of type class
  Finite (localZoom s Q W hQV hQW)

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:96:6:
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Nat.card (localZoom s Q W hQV hQW)
in the target expression
  Nat.card { L // ↑Q0 ≤ ↑L ∧ ↑L ≤ P0.W } =
    gaussian (Module.finrank (ZMod 2) ↥P0.W - a) (d - a)

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:136:55:
omega could not prove the goal; a possible counterexample was reported.

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:139:6:
Type mismatch after simplification for `retainedConditional_uniform s Q L hQV had hd`.
```

Further errors occur at lines `144`, `145`, `153`, `154`, `164`, `177`, `181`, `182`, `184`, and `190`. The complete output is in `evidence/06-direct-main.log`; extracted context is in `evidence/first-actionable-diagnostics.log`.

Per the stop-on-first-failure policy, Checks, forced combined build, independent replay, OLEAN stability comparison, signature extraction, axiom reports, forbidden-shortcut scan, and anchored-error scan were not run.

## Isolation

The accepted bundle was verified and fetched as exactly `6b522880de618597c5ec427f3dd13fd83665b76e`. The worktree was detached, linked `.lake/packages` and `.lake/build` to `/home/dfredriksen_quantyra_org/mz24-fixed-rho-de048da`, and installed only the frozen target pair. `evidence/05-installed-verification.log` records both installed hashes.

The shared local main changed after remote staging and now has SHA-256 `c6d8a61573df065e603d3cfff194218489223708468fd140dde931563c259e8b`. It was not edited or reverted by the orchestrator and did not affect this run's frozen remote input.

## VM lifecycle

- Project: `quantyra-lean-cert-20260915`
- Zone: `us-central1-a`
- VM: `quantyra-lean-builder-01`
- Final independently verified state: `TERMINATED`

This is a compilation receipt only and makes no certification claim.
