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

`node --test scripts/aws-archive-migration/logical-hardlink-20261007/second-repair-v2/test.mjs scripts/aws-archive-migration/logical-hardlink-20261007/second-repair-v2/security-test.mjs scripts/aws-archive-migration/logical-hardlink-20261007/second-repair-v2/chain-test.mjs`

After committing the successor, prepare a new protected, exclusive code supplement:

`node scripts/aws-archive-migration/logical-hardlink-20261007/second-repair-v2/prepare-supplement.mjs --output <new-protected-file>`

The supplement pins its code commit/bytes and all 305 original artifact pins,
45 catalog pins, old parent acceptance bytes and original installation/registry.
It explicitly states no fresh live authentication and unchanged data versions.
Do not replace original packet, mappings, receipts, catalogs, keys or reports.

Root independently reviews the supplement and commits BOTH of these parent files
(this author does not create them):

- `archive-general-consumer-second-repair-independent-verification.json`: type
  `archive-logical-hardlink-independent-verification-v2`, complete true,
  reviewer_role `independent-code-verifier`, verdict GO or GO-WITH-BOUNDARIES,
  code_supplement_sha256, old_packet_sha256, code_commit.
- `archive-general-consumer-second-repair-acceptance.json`: type
  `archive-logical-hardlink-root-acceptance-v2`, decision ACCEPT, reviewer_role
  `root-independent-verifier`, author_proof_is_not_independent true,
  code_supplement_file, code_supplement_sha256, independent_verification_sha256
  (exact committed review bytes), old_packet_sha256, old_root_acceptance_commit,
  code_commit. All bindings must match the reviewed supplement.

Only after that NEW acceptance, the owning operator may run:

`node scripts/aws-archive-migration/logical-hardlink-20261007/second-repair-v2/install-local-restore.mjs --root-acceptance-commit <new-parent-40hex>`

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

## Second repair (R1/R2)

The prior 7eaf68a6 code, b89c87ac supplement and CODE NO-GO review remain
historical. This v2 uses distinct parent filenames and v2 types; v1 acceptance
cannot activate it. The 15 code files are checked against exact committed bytes.
The new supplement additionally embeds exact original registry UTF-8 bytes,
old_local_registry_sha256, the exact ordered source_aliases vector and
source_aliases_sha256, aws_contract and caller_identity_evidence (the old
packet-pinned final-controls.json). These fields are covered by the supplement
hash accepted by Root; no registry field can authorize a different alias/file.
Runtime reconstructs the original registry, checks all 45 routes against the
accepted catalog vector, then allows only the exact new consumer binding. Every
registry field and every alias must match that reconstruction. The installed
body may differ in JSON whitespace/key order only. The supplement path must
also equal the path explicitly committed in the new acceptance.

Both Restore and VerifyOnly resolve quantyra credentials once, then require
GetCallerIdentity account 063280428495 and the accepted principal
arn:aws:iam::063280428495:user/ServiceAdmin before private-key reads, S3
GetObject, verification metadata writes or output creation. Account mismatch
rejects even if those credentials could read the archive. DryRun/List are local
metadata plans, make no AWS/key calls and assert no observed caller identity.

S3/STS are fixed to HTTPS regional aws/us-east-1 endpoints, ignoring ambient
global/service/profile endpoint overrides, FIPS/dualstack and profile region
settings. S3 uses path-style addressing and disables region redirects and
acceleration. Every final signed request is checked for exact host, HTTPS,
port and signing service/region before transport. Node HTTPS enforces certificate
and hostname validation with TLS >=1.2. Profile role/web-identity STS calls use
the same official transport constraint. The output receipts identify observed
account/principal and official endpoints. Profile credential acquisition is
trusted local configuration; executable providers/SSO are still subject to
their provider controls. There is no CLI/environment transport bypass. Explicit
testingCredentials/testingTransport library arguments supply local SDK fixtures
only; the active CLI always uses the production implementation.

PowerShell now delegates creation of its unique output directory to Node using
--create-workspace, after registry/root/code/caller gates. Synthetic chain tests
mock only external Git evidence and the final HTTP handler and supply invented
profile credentials, locally generated keys and encrypted envelopes. They
exercise the actual installer, generated wrappers and active entry. Test GO
objects exist only inside the isolated fixture; they are not independent review
or actual parent acceptance. The tests prove wrong-account/failed-identity and
modified-alias refusals before S3, output creation and VerifyOnly writes.
