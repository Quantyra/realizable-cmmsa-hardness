# GCP ActualOneExperimentRetainedLaw compilation

- Result: FAIL at direct main build; no repair attempted.
- Accepted Git SHA: `6b522880de618597c5ec427f3dd13fd83665b76e`
- Checkout: fresh detached GCP worktree at `/tmp/gcp-actual-one-experiment-retained-law-20260924T020235Z/checkout`
- Bundle SHA-256: `8d9dceeb328b1ae75e44f9726aca90e78d474c04d5b4deb7e4f54eb293ba0525`
- Main frozen SHA-256: `6104ab33839b08e291a82ab945374b490f51ed77ba1033874c61cc0887c4502a`
- Checks frozen SHA-256: `02211843a37230d7f289443904a173fc40d3ec260f4914461ae744429d3951c0`
- Lean: `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`
- Lake: `5.0.0-src+6a10ac8`
- Invocation: `~/.elan/bin/lake --old`
- Lean source edits by orchestrator: none
- Local Lean/Lake execution: none
- Git commit or push: none

## Build result

`~/.elan/bin/lake --old build PvNP.RealizableHardness.ActualOneExperimentRetainedLaw` exited `1`.

The first target diagnostic is:

```text
lean/PvNP/RealizableHardness/ActualOneExperimentRetainedLaw.lean:54:2:
don't know how to synthesize implicit argument `d`
```

The same declaration also reports an unresolved `d` at `54:30`. Later diagnostics include unresolved `d` arguments at `58:30` and `58:38`, a type mismatch at `59:2`, and unknown identifier `localToAmbientZoom` at `64:12`. The complete build output is in `evidence/06-direct-main.log`; extracted context is in `evidence/first-actionable-diagnostics.log`.

Per the requested stop-on-first-failure policy, the Checks build, forced combined build, independent replay, OLEAN stability comparison, theorem signature check, axiom reports, forbidden-shortcut scan, and anchored-error scan were not run.

## Isolation

The accepted bundle was verified and fetched as exactly `6b522880de618597c5ec427f3dd13fd83665b76e`. The worktree linked `.lake/packages` and `.lake/build` to `/home/dfredriksen_quantyra_org/mz24-fixed-rho-de048da` and copied only the frozen Lean pair into the detached checkout. `evidence/05-installed-verification.log` records both installed hashes.

## VM lifecycle

- Project: `quantyra-lean-cert-20260915`
- Zone: `us-central1-a`
- VM: `quantyra-lean-builder-01`
- Final verified state: `TERMINATED`

This run tests only the frozen one-draw conditional-law pushforward pair. It does not certify a decoder or CMMSA result.
