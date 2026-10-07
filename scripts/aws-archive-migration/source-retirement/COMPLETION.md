# Production archive lifecycle integration

Scope: the old research archive bucket,205 exact versions/18,579,936,167 bytes,
105 authenticated encrypted chunks and45 catalog pins. Shared CYINT session
archives/118 files are an unresolved separate ownership candidate, excluded
from every resource request, allowlist and mutation. No IAM/role/secret mutation,
payload/key retrieval, local archive cleanup, source policy apply or destination
policy apply command exists. The committed gate remains authorized=false/HOLD.

```powershell
# Default offline check: no AWS requests.
C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe -B scripts/aws-archive-migration/source-retirement/cli.py
# Authorized read-only current source permissions and unapplied freeze simulation:
C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe -B scripts/aws-archive-migration/source-retirement/cli.py permissions --output scripts/aws-archive-migration/source-retirement/evidence/new-permissions.json
# Explicit metadata-only complete namespace/configuration/HEAD/tag/ACL observation:
C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe -B scripts/aws-archive-migration/source-retirement/cli.py observe --output scripts/aws-archive-migration/source-retirement/evidence/new-observation.json
```

Every output name must be new. `permissions` performs205 exact per-version
DeleteObjectVersion simulations and one DeleteBucket simulation, with source
cyint-ea ARN, source resource owner, exact key ARN, SecureTransport=true,
PrincipalArn and per-version s3:VersionId context. It retains request IDs and
normalizes stable decision identity separately. Action, resource, truncation,
missing context and complete ResourceSpecificResults are validated. Three
additional proposal-only simulations test PutObject denial, preserved exact
GetObjectVersion and exact DeleteObjectVersion for the old source user. This
uses ResourcePolicy in the simulator and **does not apply that policy**.
IAM simulation is a preflight, not actual write authorization or an atomic lock.

## Root evidence and reachable guarded commands

`check --gate <root-file> --gate-sha256 <external-hash> --root-commit <evidence-commit>
--gate-commit <later-gate-commit> --output <new-receipt>` executes a complete
root-gated read-only production preflight. `execute` accepts the same inputs,
uses the fixed protected shared state directory and is reachable only after
all local/committed proofs pass and current source/destination policies,
inventories, exact metadata, identities and permissions meet those proofs.
Do not run execute or apply either proposed policy now.

The evidence commit contains the distinct exact root allowlist and all proof
blobs. A **separate later gate commit** contains the exact root gate at
docs/aws-migration-2026-10-06/archive-source-retirement-root-gate.json. The gate
refers to the earlier evidence commit, avoiding a self-referencing commit hash.
Both commit hashes and the gate SHA256 are external CLI pins. Root gate local
bytes must match the committed gate blob on every authorization. Exact Git
blobs are cached as immutable content; local gate/code hashes and TTLs are
rechecked on every authorization. Mutable cloud state is never cached as proof.
Unrelated later HEAD changes are allowed; reviewed executable bytes remain exact.

The existing eight typed independent attestations remain mandatory. Each must
pin the concrete underlying production proof pointer specified in root.py's
KIND_PROOFS. `production_proofs` has exactly the names/types in PROOF_TYPES.
Each pointer is {path,sha256}, relative to the fixed parent docs evidence prefix.
There is no adapter accepting generic true-only flags. The concrete contracts
require:

- Full205/410-metadata baseline with exact source/destination configuration,
  private owner ACLs, complete inventories, tags/headers and proposed freeze/
  retention policies actually present in the baseline.
- Independent full immutable hash-reuse scope and combined packet/HTTPS
  acceptance binding105 authentication,45 catalogs and exact205 mappings.
- Current per-version permission proof from permissions.evaluate, whose stable
  decision digest matches permission_proof_sha256. Full IAM simulations run
  at startup and closing; each mutation additionally requires a newly simulated
  exact target matching its independently accepted per-version decision.
- Source freeze operating readback/request ID/control custodians and producer
  topology/shutdown records, concrete local PID or root-observed remote stop
  command/service/operator/receipt, no unresolved producers, observations no
  older than five minutes at gate issue and leases covering gate expiry.
- Destination hold readback, all205 versions/45 catalogs, maintained control
  custody and key custody receipts naming symbolic key reference, custodian,
  proof hash and no source dependency. The tool never opens a key.
- Installed actual destination consumer command/config, exact destination
  versions and successfully restored size/hash; complete authoritative DNS
  inventory hash, observed matching delegation, TLS fingerprints, live HTTPS
  route response hashes and real destination deployment command.
- Whole-bucket ownership/version attribution, explicit retained shared source
  principal, no other bucket scope/unexplained data; examined dependency surfaces
  and receipt-backed destination/stopped/historical dispositions.
- Independent integration code review with exact executable hashes, reviewed
  boto3/botocore1.43.108 transport receipt and findings.

The original full205 allowlist stored SHA256 is also hard-pinned in the loader
and CLI: root cannot rebind a different set of versions. Raw authentication,
shutdown/topology, custody, DNS, ownership, dependency and transport receipts
must be linked by exact SHA256 in committed independently accepted underlying
proofs. A typed wrapper alone cannot substitute for these receipts.

Root evidence pins establish byte identity and contract coverage; root must
substantively accept the actual independent operating proofs. The code cannot
manufacture external shutdown/consumer/DNS/ownership evidence. Remote stop
records are explicitly root-observed leases, not claims of fresh remote API
probes by this tool. Local PID checks use read-only Windows native query; they
never use Windows os.kill(pid,0), which can terminate a process.

## Source and destination policy contracts

policy.source_freeze preserves the original source HTTPS deny and adds global
producer/control write denies. PutObject has **no principal exception**, so the
old source user cannot upload/overwrite either. Tags/ACL/retention/legal-hold/
restore/multipart producer operations are also denied. Unversioned deletion
(creating markers) is denied. Exact DeleteObjectVersion/DeleteBucket cleanup
is confined to the already pinned source cyint-ea principal through a separate
deny-for-other-principals statement. No new executor/user/role or broad IAM
grant is required or invented. Shared identity use outside this bucket is not
revoked. Get/read, TLS and key/catalog custody are preserved until eligibility.

policy.destination_custody additionally denies version deletion, writes and
control policy removal/replacement for everyone on the exact new archive
bucket. It supports read/restore while holding all exact versions during source
retirement. Both exact policies are unapplied proposals. A source-only freeze
is not adequate destination retention proof. Actual policy matches and all18
configuration pins are checked by the production adapter; drifting/missing
controls fail closed. These policies have no compare-and-swap API guarantee;
root owns their eventual exclusive installation and operating custody.

The final proposals passed AWS Access Analyzer ValidatePolicy with zero findings
on 2026-10-07. Bucket tagging/CORS/ownership removal APIs use PutBucket IAM
actions, covered by PutBucket*. Invalid DeleteBucketTagging/DeleteBucketCors/
DeleteBucketOwnershipControls API names were removed from the IAM action list.
See the [AWS S3 API permission matrix](https://docs.aws.amazon.com/AmazonS3/latest/userguide/using-with-s3-policy-actions.html).
The corrected source proposal was then simulated for cyint-ea: PutObject
explicitDeny, GetObjectVersion allowed, DeleteObjectVersion allowed. Neither
policy was installed.

## Transport, journal and closing observations

The production adapter lazily creates the source-only mutation client after
root preflight. DeleteObject uses exact source bucket/key/version/IfMatch/owner;
DeleteBucket uses exact bucket/owner. The SDK retry phase and regional redirects
are disabled under the pinned private endpoint hook. At actual before-send,
the client revalidates its guard and reloads the root gate/pins/TTL; expiry after
signing prevents a send. A request already sent can finish after expiry.

The runner internally locks the fixed shared protected user/SYSTEM directory,
reloads the durable chain under lock and uses one fixed retirement.journal.
Intents/confirmations are fsynced. Lost replies never trigger blind retry;
absence after intent is an observed state, not causal attribution. Present data
after ambiguous intent and any bucket reappearance, even empty, block. Torn,
changed, expired and mismatched chains remain intact; there is no renewal or
automatic successor-journal bypass. Failure receipts are immutable and distinct.

Full namespaces are checked throughout. Initial and closing sweeps verify all
exact metadata; per-version mutation sweeps freshly verify that source/target
pair while preserving complete namespace checks. This avoids redundantly
reading410 metadata records for each delete. Before every supported mutation,
its actual IAM decision and exact principal are rechecked. Final slow proof/
dependency phases precede closing full data observations and local final expiry
checks. A terminal event or receipt alone never means current state or CLI
success; post-append/receipt expiry can still fail and needs root reconciliation.

Distributed observations and IAM simulation are non-atomic. Local locking does
not exclude other hosts/cloud actors. Root must maintain source shutdown,
exclusive cleanup/control custody and destination retention through independent
post-verification. New scoped policies, code changes, runtime/SDK/transport
changes and reconciliation procedures require fresh independent review.

## Completion evidence and historical receipts

`evidence/completion-test-results-final.json` is the final code-pinned synthetic
validation receipt. Earlier preparation and completion test/manifest receipts
remain historical; they are not assertions that earlier code hashes equal
this final integration. `completion-artifact-hashes.json` pins the completed
owned artifacts, excluding itself.

`completion-live-permissions.json` records 209 read-only IAM simulations during
13:13:57?13:15:52 UTC on 2026-10-07: all206 current cleanup decisions allowed.
The current source was not frozen. Its projected-policy hash belongs to the
then-current proposal; `completion-policy-validation.json` supersedes that
projection with the final corrected, zero-finding policies and three new IAM
simulations. `completion-live-observation.json` records full205/205 inventory,
410 HEAD/tag/ACL records and closing complete namespaces/configurations during
13:17:09?13:21:12 UTC, with no markers or uploads. These observation intervals
predate final guard refinements and are historical read-only observations, not
fresh postfreeze proof or retirement eligibility. Every live receipt records
zero mutations; no GetObject, key or SecretValue operation was used.

The completed implementation still needs independent review of these exact
committed bytes and root acceptance of actual freeze/quiescence, destination
retention/custody, installed consumers/restore, global DNS/live website checks,
ownership and bounded permission/expiry operating proofs. The gate remains
disabled. No source execution, policy installation, shared principal revocation
or local source archive/data/key deletion has occurred.

At closeout, parent status records root acceptance of the original archive
custody packet plus HTTPS supplement, local installation and actual core
consumer acceptance. It still records a separate actual recovery PowerShell
consumer hardlink gap under owner repair. Those accepted earlier boundaries
are preserved; they do not establish full source retirement eligibility or
accept this new lifecycle integration. The separate logical-hardlink directory
is another owner's work and is outside this commit.
