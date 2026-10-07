# S3154 archive custody tools

Run from `C:/Users/dfred/Desktop/Projects/realizable-cmmsa-hardness` with Node 26 and the named AWS profiles `cyint-ea-prod` and `quantyra`. No AWS CLI is required by these tools. Dependencies are pinned in this directory's package and lock files. Install with `npm ci --prefix scripts/aws-archive-migration --ignore-scripts --no-audit --no-fund`.

The source is `quantyra-research-archive-485386182336-us-east-1`; the destination is `quantyra-research-archive-063280428495-us-east-1`. AWS account identities and expected bucket owners are checked. No tool deletes a source object, source version, or source bucket. GCP projects, compilers, experiments, mathematical sources and research publication are outside this implementation.

Protected inputs remain in the user profile: `.quantyra/archive-catalogs/research-archive-catalog.json` and the existing research archive key. The key is read internally, never printed, and its in-memory buffer is cleared. Detailed catalogs, mappings and payloads remain outside Git in `.quantyra/aws-migration-20261006/`. Tool stdout contains only status, counts, byte sizes and hashes. AWS response bodies, headers and exception messages are never logged.

The initial 52-object estimate is superseded by live discovery: the research bucket also contains CMMSA recovery archives. Always run discovery again before interpreting an all-bucket completion receipt. `discover` lists every object version and delete marker, follows both pagination markers, and validates all protected catalog versions. It stops beyond 100 pages. Current-version listing alone is insufficient.

```powershell
node --test scripts/aws-archive-migration/test.mjs
node scripts/aws-archive-migration/status.mjs
node scripts/aws-archive-migration/migrate.mjs discover
node scripts/aws-archive-migration/migrate.mjs preflight
```

`preflight` reads IAM simulations for the concrete bucket and object actions, checks identity, and reads versioning, public blocking, ownership and encryption controls. STS identity by itself does not authorize writes. A failed simulation, unreadable configuration or wrong account stops execution. `provision` uses the same gate plus create/configure actions and refuses to modify an existing bucket. If a creation step fails, inspect the recorded state and actual bucket controls rather than rerunning creation blindly. IAM simulation permission is itself a prerequisite.

The relay fallback uses separate source and destination credentials, up to one 8 MiB multipart part in memory, exact source versions, source metadata/tags and AES256 destination encryption. It rereads each exact new destination version and compares its byte count and SHA-256. It preserves historical versions and replays delete markers only in the destination. Ambiguous same-timestamp ordering stops execution. Completed mappings are checkpointed after verification; interrupted uploads must be reconciled before another writer starts.

```powershell
node scripts/aws-archive-migration/migrate.mjs copy-core
node scripts/aws-archive-migration/migrate.mjs copy
```

Server-side copy avoids workstation upload cost. Its temporary destination policy grants the named source user copy-only access to the `migrations/` prefix, with TLS, AES256 and exact source-prefix constraints, plus necessary copy tagging permission. It expires at `2026-10-08T12:00:00Z`. Both destination policy-management and cross-account source permissions are simulated before policy installation; the actual policy is read back and compared after AWS singleton/order normalization. An unrelated policy is never replaced. Source IAM and source bucket policies are not modified.

```powershell
node scripts/aws-archive-migration/server-copy.mjs bridge
# Only when replacing this operator's exclusive incomplete relay:
node scripts/aws-archive-migration/server-copy.mjs cancel-relay
node scripts/aws-archive-migration/migrate.mjs verify-source
node scripts/aws-archive-migration/copy-authenticate-core.mjs
```

Retain each running process handle through terminal. `copy-authenticate-core` requires source authentication receipts, streams the destination QARC1 envelope through AES-GCM, hashes ciphertext and compressed plaintext, validates every tar entry, hashes every regular member and authenticates all hardlink dependencies. Its source/destination inventories must agree before and after the copy. Previously mapped versions are authenticated again, and one unmapped version from an intentionally interrupted server-side copy can be recovered only after its hashes and metadata pass. No unmapped version is deleted. A protected exclusive lock prevents a second core writer. If the process is killed, inspect its PID and state before manually removing a stale lock; never remove a live lock.

Only selected regular log bytes of at most 64 KiB are staged for its actual restore. They become a verified artifact after all chunk, member and authentication checks pass. Tar payloads stream through memory. Whole archives are never extracted to disk. Native tar and AWS CLI are unnecessary. A separate bounded restore supports one exact regular member of at most 1 MiB; it rejects unsafe paths, symlinks/junctions and existing output files.

```powershell
node scripts/aws-archive-migration/bounded-restore.mjs source
node scripts/aws-archive-migration/bounded-restore.mjs destination
# Independent full core verification, when required by root:
node scripts/aws-archive-migration/migrate.mjs verify-destination
```

After the core pass, transfer the complete stabilized research bucket and verify the additional recovery catalogs. The server-side generic copier supports objects up to 5 GiB and stops for delete markers or larger objects; use the relay for those cases. All copied objects receive exact new version IDs and byte/hash verification. Recovery discovery downloads bounded exact-version catalogs internally, verifies their schema and records hashes. The recovered 44-directory set is complete only when all 44 catalogs are present and authenticated. The original recovery catalogs retain their source references as historical evidence; successor catalogs are separate protected artifacts.

```powershell
node scripts/aws-archive-migration/migrate.mjs discover
node scripts/aws-archive-migration/recovery.mjs discover
node scripts/aws-archive-migration/server-copy.mjs copy-all
node scripts/aws-archive-migration/recovery.mjs verify-destination
node scripts/aws-archive-migration/recovery.mjs activate
node scripts/aws-archive-migration/migrate.mjs activate
node scripts/aws-archive-migration/server-copy.mjs remove-bridge
```

The active core successor is `.quantyra/archive-catalogs/research-archive-catalog.quantyra.json`. It retains source hashes, key reference, original receipts and source version IDs, while its active bucket/profile/version IDs point to Quantyra. The whole-bucket mapping remains separately protected; adding unrelated recovery mappings does not invalidate an unchanged verified core catalog. Activation requires exact authenticated versions and an unchanged member catalog. The original catalog remains unchanged. Original AWS-CLI restore-tool bytes are preserved in protected migration history before their active entry point is replaced.

Use `restore.mjs --catalog <successor> --workspace-root <real-output-directory> --path <exact-member>` for active bounded restoration. `--dry-run` reports only counts, bytes and hashes. Keep restored raw evidence outside the public Git repository.

After both catalog sets are activated, `node scripts/aws-archive-migration/install-local-restore.mjs` preserves exact original local tool bytes and installs the existing local entry points against a verified Quantyra registry. The active Node entry accepts historical or successor catalog paths, redirects by exact catalog hash, supports count-only list/dry-run and full streamed verify-only, and performs bounded single-member restores. Old `--profile cyint-ea-prod` arguments on a registered historical catalog cannot send a consumer back to CYINT. The directory PowerShell entry uses all 44 successor catalogs without AWS CLI. Full directory extraction is intentionally outside this bounded restore interface; the preserved original tool remains available for explicitly planned full restoration with adequate disk and dependencies.

Root owns the retirement decision: require stable all-version inventory coverage, destination hashes and visibility, all authenticated catalog chunks/members, a real bounded destination restore, retained key custody, active consumer/reference verification, removal of the temporary bridge, and explicit disposition of every additional archive. Never infer retirement eligibility from fixture tests, a partial progress file, or the original 52-object estimate.

AWS contracts: [versioned CopyObject and new destination version IDs](https://docs.aws.amazon.com/AmazonS3/latest/API/API_CopyObject.html), [multipart copy threshold](https://docs.aws.amazon.com/AmazonS3/latest/userguide/copy-object.html), and [cross-account IAM simulation](https://docs.aws.amazon.com/IAM/latest/APIReference/API_SimulatePrincipalPolicy.html). These tools use direct checks and actual object reads in addition to simulation.
