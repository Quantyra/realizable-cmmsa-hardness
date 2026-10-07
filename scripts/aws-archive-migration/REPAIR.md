S3154 repairs preserve the original independent NO-GO review and historical
catalogs/receipts. No tool in this workflow deletes source objects or keys.

The original actor PID 6716 was absent at resume; its stale lock and 42 exact
version/member authentication checkpoints are retained. `repair-copy.mjs` owns
an exclusive protected `repair/writer.lock`, rejects a live original actor,
checks actual destination permissions/controls, journals each source identity
before CopyObject, reconciles lost replies, and allocates a distinct destination
version to every source version even for identical bytes. Unmapped legitimate
duplicates are hashed and retained in `repair/retained-versions.json`. Never
delete a version to satisfy inventory coverage. This is the replacement copy
entry; the historical generic server copier is disabled.

Run from this satellite, one writer at a time:

```powershell
node --test scripts/aws-archive-migration/test.mjs scripts/aws-archive-migration/repair-test.mjs
node scripts/aws-archive-migration/repair-copy.mjs
node scripts/aws-archive-migration/recovery.mjs verify-destination
node scripts/aws-archive-migration/recovery.mjs activate
node scripts/aws-archive-migration/bounded-restore.mjs destination
node scripts/aws-archive-migration/repair-verify.mjs
node scripts/aws-archive-migration/server-copy.mjs remove-bridge
node scripts/aws-archive-migration/prepare-activation.mjs
```

`recovery activate` prepares separately pinned successor catalogs and receipts;
it does not switch restore consumers. The 44 catalogs bind exact raw/canonical
catalog hashes, complete member metadata, authenticated chunk hashes and exact
destination versions. Persistent recovery authentication cache entries bind
immutable bucket/key/version and complete member/link/type/hash signatures.
Changed identities or metadata require fresh authentication. Core resumption
reuses the authenticated immutable 42-chunk evidence bound to the original
catalog hash; it streams only remaining core chunks. Tar/member bytes stream
through hashes; the bounded restore writes only one selected regular member.

Successor files use `.json.gz` to conserve limited free disk. Stored compressed
bytes have exact hashes; canonical/member hashes bind the decoded catalogs.
Restore consumers support both representations. Historical uncompressed
catalogs are never replaced.

Terminal receipts pin complete inventories, injective mappings, retained-version
receipts and executing code hashes. Both source and destination are relisted
at the end. Bridge removal reads back absence, tolerates already-absent policy,
and refuses to remove an unrelated changed policy. `repair-verify.mjs` produces
**author proof**, not independent acceptance; it reuses authenticated immutable
evidence and verifies actual exact-version headers/tags without a redundant
bulk download. Preserve original partial summary files; export fresh repair
artifacts separately.

Root must independently accept `repair/fullscope-packet.json`. This author
never creates root acceptance. Root commits these two files in the parent:

- `docs/aws-migration-2026-10-06/archive-root-acceptance.json`: type
  `archive-root-acceptance-v1`, decision `ACCEPT`, reviewer_role
  `root-independent-verifier`, author_proof_is_not_independent `true`, exact
  packet_sha256, independent_verification_sha256 and all45 `catalogs` pins.
- `archive-repair-independent-verification.json`: type
  `archive-root-independent-verification-v1`, complete `true`, versions `205`,
  and the same exact packet_sha256. Include independent findings and checks.

After root accepts, root supplies that exact parent Git commit to the prepared
switch command. The installer loads both committed root artifacts, verifies
their packet bindings, rereads all pinned evidence/code/catalog byte hashes,
and validates all authenticated member/chunk metadata before any local write:

```powershell
node scripts/aws-archive-migration/install-local-restore.mjs --root-acceptance-commit <40-hex-root-commit>
```

The author does **not** execute this switch before acceptance. Root subsequently
checks active restore consumers and routes source retirement through S3156.
AWS movement, restored logs and fixtures convey no mathematical, compiler,
hardware, publication, GCP migration or launch clearance.
