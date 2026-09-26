# GCP ZoomOutJoint baseline outcome

- Purpose: early kill test for one-experiment decoder conversion; not CMMSA certification.
- GCP project: `quantyra-lean-cert-20260915`
- VM: `quantyra-lean-builder-01`
- Zone: `us-central1-a`
- Accepted Git SHA: `6b522880de618597c5ec427f3dd13fd83665b76e`
- Remote checkout: clean, detached, isolated at `/tmp/zoomoutjoint-baseline-20260924T012706Z`
- Source transport: locally verified Git bundle because the VM could not connect to GitHub
- Bundle SHA-256: `8d9dceeb328b1ae75e44f9726aca90e78d474c04d5b4deb7e4f54eb293ba0525`
- Lean: `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`
- Lake: `5.0.0-src+6a10ac8`
- Required invocation form: `~/.elan/bin/lake --old`

## Source hashes

- `ZoomOutJoint.lean`: `6ea17417713d1b87efaa1542bf3e9b753a3acaa333217915151222e0ea311424`
- `ZoomOutJointChecks.lean`: `17a5a43b3c8f7a5c672104e39a70181077b06202e279d22c8a388783dd04913d`
- `lean-toolchain`: `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88`
- `lakefile.toml`: `03c6564b4a501867a608a3439198e41b88eedf17e3c79c6bfd01790f6ae34cbe`
- `lake-manifest.json`: `825d2e1a20005a259fdf5b181528b391dd6ba18a52c86127caf4c3be990e04f0`

## Build results

- `~/.elan/bin/lake --old build PvNP.RealizableHardness.ZoomOutJoint`: failed, exit code `1` from the GCP SSH command.
- `~/.elan/bin/lake --old build PvNP.RealizableHardness.ZoomOutJointChecks`: failed, exit code `1` from the GCP SSH command.
- First precise underlying error for both: Lake attempted to clone pinned dependency `cslib`; Git failed to connect to `github.com:443` and exited `128`.
- Classification: missing dependency / VM outbound-network infrastructure failure.
- Source/API classification: not established; the Lean compiler was never reached for either requested target.
- Lean source repair: none attempted.

## Conditional scans

The requested sorry/admit/axiom source scan and theorem-axiom scan were conditional on a successful build. Neither build succeeded, so no success-dependent scan was performed and no kernel-evidence claim is made.

## Evidence map

- `01_vm_start.log`, `01_vm_start.exit.txt`: VM startup.
- `02_checkout_metadata.log`, `02_checkout_metadata.exit.txt`: failed direct GitHub clone attempt.
- `03_bundle_verify.log`, `03_bundle_metadata.txt`: accepted-HEAD bundle creation and verification.
- `04_bundle_scp.log`, `04_bundle_scp.exit.txt`: bundle transfer.
- `05_remote_checkout_metadata.log`, `05_remote_checkout_metadata.exit.txt`: remote bundle hash, exact detached Git SHA, source SHA-256 hashes, and Lean/Lake versions.
- `06_build_ZoomOutJoint.log`, `06_build_ZoomOutJoint.exit.txt`: direct primary-module build.
- `07_build_ZoomOutJointChecks.log`, `07_build_ZoomOutJointChecks.exit.txt`: direct checks-module build.
- `08_dependency_cache_scan.log`, `08_dependency_cache_scan.exit.txt`: VM dependency-cache search.
- `09_vm_stop.log`, `09_vm_stop.exit.txt`: VM shutdown request.
- `10_vm_terminated.log`, `10_vm_terminated.exit.txt`: final VM state verification.
