# GCP ActualOneExperimentRetainedLaw r2 compilation

- Result: FAIL at direct main build; no repair attempted.
- Accepted Git SHA: `6b522880de618597c5ec427f3dd13fd83665b76e`
- Checkout: fresh detached GCP worktree at `/tmp/gcp-actual-one-experiment-retained-law-r2-20260924T021352Z/checkout`
- Bundle SHA-256: `8d9dceeb328b1ae75e44f9726aca90e78d474c04d5b4deb7e4f54eb293ba0525`
- Main frozen SHA-256: `e92dc5649125641d39d38a87d326b071b62c3c960f2a7aff5b7646c12fc8d2c9`
- Checks frozen SHA-256: `02211843a37230d7f289443904a173fc40d3ec260f4914461ae744429d3951c0`
- Lean: `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`
- Lake: `5.0.0-src+6a10ac8`
- Invocation: `~/.elan/bin/lake --old`
- Lean source edits by orchestrator: none
- Local Lean/Lake execution: none
- Git commit or push: none

## Build result

`~/.elan/bin/lake --old build PvNP.RealizableHardness.ActualOneExperimentRetainedLaw` exited `1`.

The first actionable diagnostics are:

```text
lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:75:4:
failed to synthesize instance of type class
  Fintype (localZoom s Q W hQV hQW)

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:77:6:
failed to synthesize instance of type class
  Fintype (localZoom s Q W hQV hQW)

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:81:4:
failed to synthesize instance of type class
  Fintype (localZoom s Q W hQV hQW)

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:90:6:
failed to synthesize instance of type class
  Fintype (localZoom s Q W hQV hQW)

lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:124:20:
failed to synthesize instance of type class
  Fintype Z
```

Subsequent diagnostics include a failed rewrite at `126:10`, a `mod_cast` type mismatch at `129:6`, unknown identifier `retainedConditional` at `131:17`, and further unsolved goals and downstream errors. The complete output is in `evidence/06-direct-main.log`; extracted context is in `evidence/first-actionable-diagnostics.log`.

Per the stop-on-first-failure policy, Checks, forced combined build, independent replay, OLEAN stability comparison, signature extraction, axiom reports, forbidden-shortcut scan, and anchored-error scan were not run.

## Isolation

The accepted bundle was verified and fetched as exactly `6b522880de618597c5ec427f3dd13fd83665b76e`. The worktree was detached, linked `.lake/packages` and `.lake/build` to `/home/dfredriksen_quantyra_org/mz24-fixed-rho-de048da`, and installed only the frozen target pair. `evidence/05-installed-verification.log` records both installed hashes.

## VM lifecycle

- Project: `quantyra-lean-cert-20260915`
- Zone: `us-central1-a`
- VM: `quantyra-lean-builder-01`
- Final independently verified state: `TERMINATED`

This is a compilation receipt only and makes no certification claim.
