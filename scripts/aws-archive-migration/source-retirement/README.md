# Archive source retirement preparation — S3152/S3154/S3156/E003

Preparation only. Source eligibility is HOLD. `cli.py` defaults to an offline
check and rejects `execute` before creating an AWS session. No command applies
the producer freeze, creates root acceptance, switches consumers, revokes an
identity, accesses source IAM/secrets, deletes local files or changes AWS data.
Existing migration code, packet, catalogs, keys and HTTPS supplement are intact.

Run with the installed embedded Python (which needs the entrypoint's explicit
module path) from this satellite:

```powershell
C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe -B scripts/aws-archive-migration/source-retirement/cli.py
node scripts/aws-archive-migration/source-retirement/bind-proof.mjs --verify-only
C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe -B scripts/aws-archive-migration/source-retirement/test_safety.py
C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe -B scripts/aws-archive-migration/source-retirement/test_transport.py
```

Explicit `cli.py observe --output <new-file-in-existing-owned-directory>` uses
source `cyint-ea-prod` and destination `quantyra` profiles for metadata/STS only.
Every S3 call binds ExpectedBucketOwner. It reads complete unprefixed versions,
markers and multipart uploads with bounded pagination (100 pages, 10,000 rows),
18 bucket configuration APIs and every exact-version HEAD/tag/ACL. It compares
complete headers except copy-assigned version, timestamp and ETag; tags and
private owner ACLs must match their accepted account. It closes with both full
inventories/configurations and exact identities. No object payload or key is
read. An immutable file and cooperative exclusive lock protect owned output;
a stale lock requires investigation. Namespace drift/extras/markers/uploads
fail closed. This is distributed observation, not a transaction or freeze.

The original observation spans 2026-10-07T12:01:36.104761+00:00 through
12:05:04.420646+00:00. It records 205 versions in each bucket, zero markers or
uploads, 410 exact-version metadata records, and unchanged closing inventories
and configurations. Permission simulation was **not run**: source IAM access is
outside this preparation. The initial observation predates the new code-pin
capture and comparison fields; `metadata-preservation.json` separately runs the
current comparator over its immutable bytes without new cloud requests. Future
observations bind their executing code before/after. These receipts do not
certify present state or independent hash acceptance.

`bind-proof.mjs` streams all305 pins from packet SHA256
713abbeaeb65c456a1ba333ed0d8c77f7da8ba756085b42cd4493653ecd648ce, checks all45
catalog pins and exact source/mapping/destination row identities, and prepares
205 injective mappings totaling18,579,936,167 bytes. It never decodes catalog
member data. `bound-allowlist.json` is an **author proposal**, not a root allowlist.
Stored-byte hashes and sorted-key UTF8 canonical hashes are distinct. Canonical
JSON here preserves array order, has no spaces, and uses unescaped UTF8. Original
packet JSON.stringify row hashes are checked in their original representation.

## Required root integration

The disabled gate is a schema template, not an approval. A separate root owner
must commit an exact byte copy of the reviewed allowlist at
`docs/aws-migration-2026-10-06/archive-source-retirement-allowlist.json` plus
substantive typed acceptance attestations and underlying proof blobs. Root
supplies the exact evidence commit and external gate SHA256. The gate fixes
both bucket names, source485/cyint-ea and target063/ServiceAdmin principals,
full205 packet/allowlist, all code bytes, configuration/metadata/hash-scope and
permission pins, preservation rules and a lifetime of at most one hour.
The gate pins the fixed shared protected state directory
`~/.quantyra/aws-migration-20261006/source-retirement-execution`; the runner locks
it internally and reloads the durable chain under that lock before using a
cached Journal. Future integration must secure its Windows user/SYSTEM ACLs.
Later disjoint repository HEAD movement is allowed; reviewed file bytes and
the committed evidence blobs must remain exact.

All eight kinds in safety.KINDS are mandatory: independent archive acceptance
(including HTTPS supplement), installed actual destination restore/consumer,
global authoritative DNS/delegation/TLS/live site, whole-source ownership,
maintained producer quiescence, destination retention/key custody, active
dependencies/retained shared exceptions, and independent retirement code review.
Each root attestation has type `archive-retirement-attestation-v1`, matching
kind, decision ACCEPT, root-independent-verifier role, packet/allowlist hashes,
observed_at, valid_until covering gate expiry and nonempty underlying_proofs
with committed path/byte hashes. Hash/schema checks establish identity, not the
truth of operating evidence. Root must substantively assess the proofs.

An accepted immutable hash reuse scope must have type
`archive-independent-hash-reuse-v1`, reviewer_role root-independent-verifier,
versions205, encrypted_chunks105, recovery_catalogs44, exact full scope
{packet_sha256, source, destination, rows, catalogs, packet_artifacts}, an
authentication_proof_sha256 and version_metadata_sha256. Every present version
still needs fresh exact-version metadata compared to the accepted baseline.
Never accept historical verified flags as current custody/authentication.

`retirement.run` is a prepared injected state machine, **not wired to AWS**.
Future integration must provide the documented adapter with substantive fresh
dependency checks, complete owned inventories, exact baseline comparisons,
current configurations and IAM simulation. Action/resource/missing-context/
truncation validation is mandatory in check-only too. Permission proof covers
DeleteObjectVersion on every unique key ARN and DeleteBucket on the exact old
bucket; version IDs are independently constrained by the allowlist. It must
reload `load_gate` using Git blob reads and current exact code pins on every
authorization call, maintain external hash provenance, protect state ACLs, and
serialize every runner across the execution scope. No permissive adapter is
provided. Do not enable the CLI until this integration has its own independent
review, mocked negative tests and actual operating evidence.

## Future mutation and recovery contract

An exclusive lock and fsynced, append-only hash-chain journal bind gate and
allowlist bytes. Each version/bucket gets intent before one SDK invocation and
confirmation only after current absence plus preserved destination proof.
The prepared botocore1.43.108 client disables endpoint `_needs_retry` entirely,
including regional redirect retries, and checks guard identity/config on reuse.
18 installed-SDK synthetic transport cases cover two operations with transport
errors,500/503/429 and301/307/400 region redirects, with sockets forbidden.
The private hook must be re-reviewed after runtime/SDK/custom transport changes.

Lost replies permit readback only. Present data after intent blocks further
mutation; absence after intent is reported as observation, not proof that this
request caused deletion. A source bucket observed after any bucket intent or
confirmation blocks even when empty. Never skip fresh state because a terminal
journal event exists. No automatic journal renewal, expired-run handoff or
reconciliation bypass exists. Preserve all torn, ambiguous and expired bytes;
root/owner reconciliation needs a new independently reviewed procedure.

The engine authorizes after slow dependencies/identity reads, after durable
intents and immediately before requests. Final slow sweeps precede closing
full source/destination proofs and final expiry checks. A request begun within
expiry can finish after it; authorization controls local invocation start.
An expiry after terminal append prevents a returned success. Journal events
alone never establish successful execution or current cloud state. Local locks
do not serialize other hosts or remote actors; distributed observations cannot
exclude drift after a last read. Root must maintain producer shutdown and
destination retention through independent post-verification.

`source-freeze-proposal.json` is an unapplied statement fragment with an
unresolved dedicated executor exception. Preserve the existing HTTPS policy;
never replace it blindly. Stop schedulers/producers and prove write denial,
control-plane custody, whole inventory and no multipart uploads operationally.
Keep source Get/read access and client encryption keys, original catalogs,
history, object hashes/mappings and metadata receipts. Shared SourceUser,
cyint-ea and all roles are retained. No GCP/research/Lean/hardware/publication
authorization follows from this work.
