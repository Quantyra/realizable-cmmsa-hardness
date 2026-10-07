# Logical-hardlink restoration successor with bounded validation

This separate versioned implementation preserves every byte/path of the old
packet-pinned consumer. The existing installed wrappers still execute the old
consumer. Nothing here automatically upgrades or reauthenticates live data.
The directory-local Git attributes preserve exact successor bytes across checkout
instead of allowing automatic CRLF conversion to invalidate code pins.

The successor preserves exact-file, prefix/directory, repeated --path and full
core restoration; PowerShell Restore with no RelativeFile restores the selected
directory, and RelativeFile may be a directory prefix. Production restoration
has no 1 MiB file/output cap. --bounded (PowerShell -Bounded) explicitly selects
one exact logical member at most 1 MiB for validation. Dependency envelopes can
be larger. Raw content-addressed paths remain outside recovery directory scope.

It validates the complete catalog and link graph, stages each selected terminal
regular content once, authenticates every requested logical link and all complete
chunk dependencies, then exclusively copies regular files to safe logical paths.
Both logical and content metadata digests, catalog digest and exact version/hash
identities are included in receipts. It never creates filesystem hardlinks or
symlinks. Before key reads or archive requests it checks all output targets and
available disk for unique staged content plus all materialized output bytes,
rounded allocation and per-file/directory metadata allowances and 1 MiB headroom.
Dry-run budgets assume 4 KiB blocks; actual preflight uses the filesystem block size.
Existing output, traversal, missing/cyclic/mismatched links, collisions and
unauthenticated chunks reject.
The original verifier authenticates gzip plaintext, not an uncompressed tar hash.

Synthetic tests (no live key/client/consumer installation):

`node --test scripts/aws-archive-migration/logical-hardlink-20261007/test.mjs`

After committing the successor, prepare a new protected, exclusive code supplement:

`node scripts/aws-archive-migration/logical-hardlink-20261007/prepare-supplement.mjs --output <new-protected-file>`

The supplement pins its code commit/bytes and all 305 original artifact pins,
45 catalog pins, old parent acceptance bytes and original installation/registry.
It explicitly states no fresh live authentication and unchanged data versions.
Do not replace original packet, mappings, receipts, catalogs, keys or reports.

Root independently reviews the supplement and commits BOTH of these parent files
(this author does not create them):

- `archive-recovery-hardlink-independent-verification.json`: type
  `archive-logical-hardlink-independent-verification-v1`, complete true,
  reviewer_role `independent-code-verifier`, verdict GO or GO-WITH-BOUNDARIES,
  code_supplement_sha256, old_packet_sha256, code_commit.
- `archive-recovery-hardlink-acceptance.json`: type
  `archive-logical-hardlink-root-acceptance-v1`, decision ACCEPT, reviewer_role
  `root-independent-verifier`, author_proof_is_not_independent true,
  code_supplement_file, code_supplement_sha256, independent_verification_sha256
  (exact committed review bytes), old_packet_sha256, old_root_acceptance_commit,
  code_commit. All bindings must match the reviewed supplement.

Only after that NEW acceptance, the owning operator may run:

`node scripts/aws-archive-migration/logical-hardlink-20261007/install-local-restore.mjs --root-acceptance-commit <new-parent-40hex>`

The installer rejects old acceptance and changed/uncommitted code/data BEFORE
local writes, then preserves old installed tools/registry in a distinct history.
It leaves the original local-restore-installation.json intact and writes a new
receipt. Installation is multiple local file operations, not an atomic filesystem
transaction: preserve exclusive local writer ownership and inspect/reconcile a
partial failed installation rather than rerunning blindly. Original validators'
filesystem check/use races also require exclusive output-directory ownership.
Output publication is also multiple filesystem operations, not an atomic batch;
a filesystem I/O failure after authentication may leave an authenticated partial
subset. Existing output is never overwritten, and all authentication failures
occur before publication. Inspect partial results rather than deleting unique
output or claiming a completed restoration. Disk preflight is observational and
can become stale if another process consumes space; fail closed if statfs fails.

The successor runtime rechecks new committed acceptance, supplement/code commits,
all original artifact pins and registered catalog scope before any key/client
operation; the old registry cannot authorize it. Directory routing additionally
compares the selected directory with the pinned decoded catalog, so selecting a
raw content-addressed member does not certify the recovery PowerShell interface.

Pending after code review/acceptance: actual reinstallation, installed hashes and
one real directory44 PowerShell -Bounded logical restore (small two-envelope case), with
account/version/content/output hashes only. Never execute restored bytecode.
No source cloud writes, scientific launch, compiler run, GCP change or publication
is authorized by this code repair or its synthetic tests.
