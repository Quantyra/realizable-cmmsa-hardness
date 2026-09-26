# GCP ZoomOutJoint baseline retry

- Result: PASS
- Accepted Git SHA: `6b522880de618597c5ec427f3dd13fd83665b76e`
- Checkout: fresh, clean, detached GCP worktree at `/tmp/zoomoutjoint-baseline-retry-20260924T014605Z`
- Bundle SHA-256: `8d9dceeb328b1ae75e44f9726aca90e78d474c04d5b4deb7e4f54eb293ba0525`
- Lean: `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`
- Lake: `5.0.0-src+6a10ac8`
- Invocation: `~/.elan/bin/lake --old`
- Lean source edits: none
- Local Lean/Lake execution: none
- Git commit: none

## Dependency resolution

The worktree linked `.lake/packages` and `.lake/build` directly to `/home/dfredriksen_quantyra_org/mz24-fixed-rho-de048da/.lake/packages` and `.lake/build`. The base manifest, lakefile, and toolchain hashes matched the accepted checkout. All 11 package repositories were present, including `cslib` at `d9be64196bf145edd019f1ccfeaee0c11166ba6b`.

## Build results

- `~/.elan/bin/lake --old build PvNP.RealizableHardness.ZoomOutJoint`: exit `0`; build completed successfully with 2462 jobs.
- `~/.elan/bin/lake --old build PvNP.RealizableHardness.ZoomOutJointChecks`: exit `0`; build completed successfully with 2463 jobs.
- Anchored Lean error/panic scan: no matches.

## Conditional scans

- Eight requested theorem axiom reports were emitted. Each contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden shortcut scan over `ZoomOutJoint.lean` and `ZoomOutJointChecks.lean`: PASS for `sorry`, `admit`, `unsafe`, `native_decide`, and axiom declarations.

## VM lifecycle

- Project: `quantyra-lean-cert-20260915`
- Zone: `us-central1-a`
- VM: `quantyra-lean-builder-01`
- Final verified state: `TERMINATED`

The accepted bundle remains at `../gcp_zoomoutjoint_baseline_20260924T012706Z/accepted-head.bundle`; `02_bundle_verify.log` records its verified remote hash and exact contained ref.
