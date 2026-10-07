# Independent source production repair review

2026-10-07. Independent source production repair reviewer, native Codex session. Parent S3152/S3156/S3157/E003. Dispatch: `source-production-repair-review-dispatch.txt`. Primary workspace: `C:/Users/dfred/Desktop/Projects/realizable-cmmsa-hardness`; website inspection was read-only. The original independent review, both terminal repair-owner reports, actual commits, final implementation bytes and preserved evidence were inspected. This review does not replace the original negative review.

**Archive CODE GO with the operating boundaries below. Website CODE NO-GO. Global SourceEligibility HOLD.** Neither verdict authorizes a live operation or certifies the complete migration.

| Lane | Exact reviewed commits | Code verdict | Live eligibility |
| --- | --- | --- | --- |
| Archive source retirement | `98da0a078ec8e223a21a71801b060c0b0a148875` | GO: A1/A2 repair verified, conditional on genuine operating receipts and controlled execution | HOLD |
| Website source lifecycle and S3157 replay integration | `617791bd97a4d8aafa3d452c4e9c0b1f265cbc3a`, `cc004fd3b2e37c9988dcb991b2b887116a5ad6e1`; final evidence HEAD `b73ad4f368c23a15cf2ca97d94e09787106ef62c` | NO-GO: successful freeze-transition HTTP 204 is rejected; related ACM inventory remains incomplete | HOLD |

## Scope, exact bytes and preservation

Source remains `cyint-ea-prod`, account `485386182336`, `arn:aws:iam::485386182336:user/cyint-ea`. Destination remains `quantyra`, account `063280428495`, `arn:aws:iam::063280428495:user/ServiceAdmin`. The archive allowlist is exactly `quantyra-research-archive-485386182336-us-east-1` to `quantyra-research-archive-063280428495-us-east-1`: 205 immutable mappings, 18,579,936,167 bytes, 105 encrypted chunks and 45 catalog pins. The website allowlist remains `quantyra-website`, 112 original null mappings, source CloudFront `E1YKX9P25CCTN8` and ACM `d0b6eecb-bd1c-437d-a82f-fadf99895aa7`; destination bucket `quantyra-website-063280428495-us-east-1`, CloudFront `EFNS26JKDEMJO`, ACM `ed72ab8f-f839-49d4-a75a-d1d5081e1472` and Route53 zone `Z0765812BNRBG5KQGYTU`.

The archive commit changes 84 paths, all inside its owning source-retirement directory. All 112 tracked paths in that directory match the reviewed Git blobs, accounting explicitly for Git text CRLF normalization. The website commits change 21, 5 and 20 paths respectively, all in the authorized lifecycle/Route53/evidence scope. All 25 tracked lifecycle paths and `route53.mjs` match final committed bytes. Raw SHA-256 manifests independently bind the actual working bytes; text normalization is not substituted for those raw pins. Both HEADs and the tracked bytes remained unchanged during verification.

Independent checks matched the archive's 111-entry final manifest, 115 retained repair-fixture pins, all 193 original-review fixture pins, 234 prior own/review evidence pins and all 36 original-review indexed artifacts. The website's 19-entry evidence manifest and 449 protected tracked-file hashes match. All 2,139 installed Python runtime file pins match the owner's sealed inventory. These collections overlap; they are not additive preservation counts.

Important exact hashes:

| Evidence | SHA-256 |
| --- | --- |
| Archive final manifest `final-artifact-hashes-v3.json` | `d080d6f6310117244c4575a94717a60a33650e497aa102d01f697f14bb72dcb0` |
| Archive installed runtime inventory | `fa63c7698e7b26708a1bd666a2c0189403d68b7a1796d9488ed19d50bc2ec706` |
| Original archive packet | `713abbeaeb65c456a1ba333ed0d8c77f7da8ba756085b42cd4493653ecd648ce` |
| Original stored archive allowlist | `5856b4c5b62173c5e4fb0f7a3e24299d75414fa2365d3b1d14cd05f0768c2ea8` |
| Archive HTTPS supplement | `ba9a2880792fc6f1e59ca5bdd95ac4d76276638ddeef747fdb1e814a07914a65` |
| Final website tooling | `f9f4114018f5fc52a3073554a0cb361460075ef1d6f8a5f65c179f5db4dba390` |
| Website verification index | `f95d33a274eb874e083ae8373d8edf226cb04b0499cb6836502820ed5990087a` |
| Original website source manifest | `724fb7349cae1dff0ec55308dbd953b3fb4c941c8b0c181ae96ee5a59dd822a0` |

The independent original305 binder passed in verify-only mode: all 305 original artifact pins, 45 catalogs, exact 205 mappings and original byte total remain fixed. It performs local metadata/artifact hash verification without key access or catalog decoding; it does not reauthenticate object payloads or establish current cloud custody. SourceSLR, shared IAM, the separate 118-file CYINT archive candidate, general recovery-consumer implementation, research, GCP, Lean, hardware and publication are outside this review. Inherited retry/capture and other-owner working-tree artifacts were preserved.

Evidence and reproducible probes are under `C:/Users/dfred/Desktop/Projects/realizable-cmmsa-hardness/docs/aws-migration-2026-10-06/source-production-repair-review/`. `evidence-index.json` indexes the review files; `evidence-validation.json`, `runtime-preservation-validation.json`, `service-receipt-validation.json` and the test result files provide exact checks. Original findings, failures, scripts and fixtures were preserved, including the owners' development failures and unsuccessful disposable runs.

## Remaining website findings

### R1 — MEDIUM: an authentic successful HTTP 204 freeze transition cannot satisfy the loader

`Quantyra-Website/scripts/aws-migration/source-lifecycle/packet.mjs:128` requires `journal.requests[0].httpStatusCode === 200` when a policy edit changes the mutable bucket CreationDate. The final disposable service receipt records successful `PutBucketPolicy` responses with HTTP 204. The owner corrected its disposable harness to accept 204, but the production Root packet validator still rejects that result.

The independent probe uses the real current `loadPacket`, full original baseline, exact resources and two genuine separate synthetic Git commits. A complete Root-accepted policy-induced marker transition with HTTP 200 loads successfully. Changing only the bound installation receipt's status to 204, resealing the transition/baseline/allowlist and committing fresh evidence and a later gate makes the real loader refuse with `SourceFreezeOnlyInstallationJournalRequired`. No AWS factory or mutation is used. This is a reachable availability/production-contract defect when the accepted policy installation changes the marker, not a claim that every policy edit must change CreationDate.

Retained 204 fixture: `tmp/spr/website-production-packet-jfhF7e`; evidence commit `4456f960e5de94c7034b735beaf2266e5b329319`, later gate `2050a2848b98b37c90a55b22d73ff8f85deab368`. The accepted 200 comparison is independently retained in its earlier commits. Details: `independent-website-new-results-first.json`, case `R1-successful-204-freeze-transition-rejected`.

The real final service receipt includes `PutBucketPolicy` HTTP 204/request ID `4Z4NQFXFW0NMYWAQ`. AWS's API page itself shows 200 in its response description and 204 in its general-purpose-bucket sample response. Both documented forms and the measured receipt must be handled without falsifying receipt status. [AWS PutBucketPolicy](https://docs.aws.amazon.com/AmazonS3/latest/API/API_PutBucketPolicy.html).

Required repair: recognize the supported successful statuses while retaining actual request IDs/status, exact policy/resource/principal, independent continuity acceptance and the prohibition on creation/deletion/recreation in the transition. Add a valid 204 production-loader regression and retain the 200 and additional-operation negatives.

### R2 — MEDIUM: fresh ACM reads still cannot establish complete related-certificate inventory

`collector.mjs:116` and `:178`, and `dns-cleanup.mjs:15`, call `ListCertificates` with statuses but no key-type inclusion. Default ACM filtering omits EC certificates and other non-default RSA types. The collector's related-certificate filter at `:117` additionally recognizes only `quantyra.org` and `*.quantyra.org`; it misses a certificate whose sole domain is `www.quantyra.org`. It also ignores `HasAdditionalSubjectAlternativeNames`, so relevant names beyond the summary limit are not resolved with metadata-only Describe calls.

Four independent reproductions passed on final production modules:

1. A synthetic EC certificate for `quantyra.org` appears during the preflight IAM dependency phase. The fake service applies documented default key-type filtering. Opening and closing requests both omit inclusion, the new certificate remains hidden, and the collector returns success.
2. A returned additional RSA certificate for `www.quantyra.org` is present in both inventories, yet the collector returns success rather than `UnexpectedSourceCertificateInventory`.
3. A returned RSA summary has 100 unrelated SAN summaries and `HasAdditionalSubjectAlternativeNames=true`; its full Describe metadata includes `quantyra.org`. No Describe of that additional certificate is requested, and the collector returns success.
4. The actual DNS absence helper marks `inventory.complete=true` after the same default-filtered request. Its exact old-ARN Describe absence remains useful, but the complete-inventory claim is unsupported.

These are controlled metadata reproductions, not claims that additional production certificates currently exist. The old ARN's authenticated absence is not disproven; full related-source inventory and dependency checking are incomplete. The refined final cases and exact requests are in `independent-website-new-results.json` and `independent-website-R2-refined.log`.

AWS documents non-default key inclusion and the 100-SAN summary limit with `DescribeCertificate` needed for full names. The ListCertificates and Filters pages differ on which default RSA sizes are included; both establish that the EC case is excluded without an explicit filter. Current ListCertificates documentation also describes a default key-pair-origin exclusion that a claimed complete inventory must address. [ACM ListCertificates](https://docs.aws.amazon.com/acm/latest/APIReference/API_ListCertificates.html), [ACM Filters](https://docs.aws.amazon.com/acm/latest/APIReference/API_Filters.html), [ACM CertificateSummary](https://docs.aws.amazon.com/acm/latest/APIReference/API_CertificateSummary.html).

Required repair: explicitly cover the complete supported algorithm/origin inventory under the reviewed SDK contract, validate pagination and response completeness, cover both pinned aliases and relevant wildcard names, and resolve truncated SAN metadata before assessing related resources. Keep deletion restricted to the original ARN. Do not silently adopt or delete an additional certificate. Apply the complete-inventory contract to closing and DNS absence receipts and their permanent-overlay consumers.

## Original finding dispositions and credited repairs

| Original finding | Independent repair disposition |
| --- | --- |
| A1 ambient archive endpoints | Repaired. Every production S3/STS/IAM constructor fixes official endpoint, us-east-1, partition/TLS and configured-override suppression. Cached reuse and signed requests revalidate endpoint/signing scope. |
| A2 replacement archive bucket before intent | Repaired within creator/name/control custody. Changed marker is rejected before intent, after signing and at closing/reconciliation. CreationDate is treated as mutable evidence. |
| W1 uncommitted website packet | Repaired. Explicit evidence commit, distinct descendant gate commit, fixed Root allowlist, baseline, review and recursive receipts are committed and rechecked on authorization. |
| W2 authorization expiry at physical send | Repaired. Real signed SDK request waits for authenticated TLS; bound authorization runs immediately before `req.end`. Warmed signer expiry and byte drift yield zero physical HTTP sends. |
| W3 terminal expiry | Repaired for the reviewed lifecycle paths. Checks repeat after fsync, lock release, client destruction and before CLI success rendering; durable terminal evidence survives refusal. |
| W4 stale closing bucket/old certificate | Original stale-read reproductions are rejected. Complete source/destination data/control sweeps and intervals are credited. Related ACM completeness remains deficient under R2. |
| W5 resource-specific IAM denial ignored | Repaired. Exact action/resource/context and resource-result consistency, missing context and explicit complete pagination are validated. |
| W6 never-versioned cleanup contract | Repaired for the known null-object scope. VersionId is omitted; owner/key/IfMatch remain exact, both effective deletion permissions are checked, versioning drift rejects, and global write/control denial remains. R1 still affects actual freeze-transition acceptance. |

Archive `aws.py:9`/`:28` validate the actual endpoint/partition/configured and signing region/TLS and signed AWS request host/scope. Its four environment/profile override matrices cover all five read client/account combinations and both mutation operations. Official endpoint dispatch and the one-mutation-send protections passed installed-SDK error/redirect tests; no additional mutation retry was introduced. Explicit fake transport ports remain confined to synthetic tests.

Archive `inventory.py:75`, `adapter.py:143`/`:150`, and `root.py:92` onward now bind paginated creation markers to separate Root-reviewed prefreeze/postfreeze observations, the actual freeze transition, and accepted actual creator shutdown/name control. The before-intent replacement reproduction preserves all 205 prior confirmations, presents matching configuration and an empty replacement bucket, and now fails `CONFIGURATION_DRIFT` after one marker read: zero sends and no bucket intent. Its fresh fixture evidence commit is `ecfe8c251ff35b5218ee49a585faac50afc0d3c1`; gate commit `9579ef5a6c518ca76e27fbe74f2c85a23d809db1`; gate hash `dec98bd743ddb4dd38c210998647cf023d7850fadaa4997e6ba8f3555a0ed753`. Signing-time drift preserves intent but sends nothing. Closing/reconciliation reject reappearance. Accepted policy-induced marker transition passes; missing/unaccepted creator, nameguard or freeze-journal receipts reject.

CreationDate is not an immutable bucket instance ID, and matching-marker recreation cannot be excluded by this metadata alone. Actual independently assessed creator shutdown, name protection, policy/root custody and exclusive operating ownership must continue through independent post-verification. Read denial or incomplete marker observation fails closed. These are ordinary external operating boundaries, not manufactured control effectiveness. [AWS bucket marker semantics](https://docs.aws.amazon.com/AmazonS3/latest/API/API_Bucket.html), [AWS endpoint override behavior](https://docs.aws.amazon.com/sdkref/latest/guide/feature-ss-endpoints.html).

The website Root review pin uses a reviewed ancestor commit plus exact bound code/tooling bytes, permitting evidence-only descendants without circular gate/evidence hashing. Permanent retirement-control data is excluded from the tooling digest and independently pinned through committed control/Root artifacts; tampering, missing data and descendant downgrade are refused. Source producer/controller shutdown and Root custody remain material independent acceptance requirements, not satisfied by schema booleans. Both production gates and the real durable retirement control remain disabled.

## Disposable service evidence and S3157 replay integration

No disposable cloud fixture was created, modified or cleaned by this reviewer. The owner's immutable service receipts were independently checked for exact destination bucket/owner/request contract, request IDs, stored data hashes, compiled policy and final empty namespace/absence. The final fixture policy exactly equals the current compiler rebound to destination resources with the sole documented `DeleteBucketPolicy` recovery exception. Its stored hash uses raw `JSON.stringify(policy)`, not the canonical object digest: `2bb4b922934bb969b66400334f079977c6e9c7fac3b606a7c925c746a0c0b1d1`.

The final 46-byte synthetic-object digest is `3b11c272886e70fa168642dbc24842c957c87d13346696277df43a204a79008d`. The final receipt SHA-256 is `50a592b1d968c33532010f07ef5b01297b5392ef209745a9fe22afc727d3affe`. It records 40 exact bucket requests with service request IDs, three matching stored object hashes, denied overwrite/versioning/unknown cleanup (403), wrong IfMatch (412), successful known-key deletion (204), and subsequent absence. The request omits VersionId and successful deletion returns no version/marker. Production freeze has no recovery exception.

| Owned disposable bucket suffix | Preserved outcome | Empty history request ID | Final owner-checked HeadBucket 404 request ID |
| --- | --- | --- | --- |
| `79edcc4d-d42b-4053-b21b-6f2521d173a1` | Original run failed cleanup; separate recovery records three verified hashes, policy/object/bucket cleanup | `FA5JRJAEXGJVQ6BG` | `636YQW8CNNDHQPVD` |
| `985fb1e0-1e31-4d4c-adfd-05c074c891e7` | Contract experiment failed; cleanup succeeded | `ECXXSMQ2DC5PE2Y4` | `ECXQ8Q669XP44TPC` |
| `15b14ce3-24a2-41c1-a1b6-6caf270c17ed` | Full repaired contract and cleanup succeeded | `Z8WEMMDHBB71T5WR` | `JHR15W3K9K02CEVZ` |

Each bucket has the prefix `quantyra-migration-fixture-`. All relevant final/recovery requests are owner-pinned to destination account 063; none uses Source. The recovery code checks the destination STS identity, although its recovery receipt does not separately retain that STS result. Request IDs and committed receipts establish auditable recorded evidence and internal consistency; they are not cryptographic proof of service origin or a fresh observation of current cloud state. No prior failed experiment is relabeled as a successful contract run.

The owner's version-only-deny/no-VersionId experiment recorded 204, whereas current AWS deletion guidance says either explicit deletion deny blocks unversioned deletion. That discrepancy and propagation limits remain explicit. The repaired contract permits/checks both deletion permissions and does not depend on the deny-only experiment. IAM simulation is not AWS authorization. [AWS deletion guidance](https://docs.aws.amazon.com/AmazonS3/latest/userguide/DeletingObjects.html), [IAM simulation limits](https://docs.aws.amazon.com/IAM/latest/APIReference/API_SimulatePrincipalPolicy.html).

The durable S3157 overlay requires separately committed Root evidence/gate hashes, an independent review and exact old-ARN authenticated absence receipt. It pins only `_1570c224b27c86e2fec72eef9a9181a4.quantyra.org.` CNAME to `_22e8f5cc9603a6193da01b2ddd7dacd2.jkddzztszm.acm-validations.aws.`. It remains disabled in the real repository. Independent execution of the exact final `importZone`, `plan` and `stage` function bodies through synthetic ports confirmed historical export preservation, suppression during re-import/plan, rejection of old desired plans, filtering of stale staged snapshots, before-batch checks, zero staging sends on a changed retired RRset, and preservation of destination validation/mail. The functions were derived byte-for-byte with AWS/control/filesystem ports rebound into retained local fixtures; the real suppression/normalization modules were imported directly. No real Route53 command ran.

`dns-cleanup.mjs` emits only a disabled exact DELETE proposal with actual RRset TTL, zone hash and fresh old-certificate absence/provenance checks; there is no Route53 writer. Actual deletion and authoritative/API absence proof remain Root/S3157 work. R2 must be repaired before its complete-inventory evidence can be accepted. Historical exports and destination validation records must remain preserved.

## Independent verification and limits

| Verification against final committed production bytes | Result |
| --- | --- |
| Archive safety | 45/45 pass; 84.911 seconds inside suite |
| Archive installed-SDK transport | 2/2 pass, including 18 operation/error/redirect subcases |
| Archive endpoint provenance | 2/2 pass with four override matrices and wire/TLS/signing drift negatives |
| Archive production integration | 26/26 pass; 578.750 seconds inside suite |
| Adapted original archive SDK/permission/refusal probes | 5/5 pass |
| Adapted original archive replacement-before-intent execution probe | PASS; zero sends, no bucket intent |
| Original305/45/205 binder and archive default CLI | PASS, local and zero requests |
| Website lifecycle safety/integration/repair suites | 40/40 pass |
| Website migration regressions | 16/16 pass |
| Adapted original website defect/negative-control probes | 8/8 pass |
| New website R1, warmed actual-SDK/TLS checks and R2 cases | 7/7 expected assertions pass; R1 and R2 reproduce remaining defects |
| Refined R2 metadata fixtures | 4/4 pass; replaces the earlier R2 evidence, not an additional coverage count |
| Actual import/plan/stage function-body replay reproduction | PASS |
| Both website default CLIs | PASS, local and disabled |

There are 131 prescribed suite tests and 22 additional independent scenarios, plus binder/default/evidence checks. Passing reproduction assertions are not code approval: they explicitly prove R1/R2 defects. Runtime is Python 3.13.7, boto3/botocore 1.43.108, urllib3 2.8.0, Node v26.5.1 and website AWS SDK 3.1147.0.

The reviewer's initial Python wrapper replaced the socket class before importing SSL, causing import-time TypeError in all four archive suites. It made no service requests. Logs remain intact. Importing SSL first corrected the wrapper; all four suites then reran fully without source or assertion changes. The initial evidence-validator policy comparison used the canonical representation rather than the owner's raw JSON-string hash; `service-receipt-validation.json` independently corrects that representation mismatch and verifies exact compiled policy equality. Original reviewer mistakes are retained rather than misrepresented as production defects.

Tests used synthetic credentials, socket/network-denying wrappers, explicit SDK/HTTP ports and locally cached public website test bytes. They executed no real AWS request or mutation, accessed no real credential/key/remote object body/secret value, performed no scientific execution and changed no production code or production Git state. Synthetic Git repositories were used only for committed-evidence tests. Writes are confined to new local review evidence/retained synthetic fixtures and the two prescribed parent report files. No parent commit, push, publication, source/destination write, GCP, Lean or hardware operation occurred.

The recorded final website read-only preflight spans 2026-10-07T15:24:58.669Z to 15:27:41.996Z, with its closing sweep from 15:27:19.437Z. It binds 112 source/null-version and 112 destination mappings, 13,594,974 bytes, no extra versions/markers/uploads, unchanged recorded source controls/policy and corrected destination HTTPS policy, 116 permission aggregates/224 exact object-action results, and a destination certificate still `PENDING_VALIDATION`. Those receipts are credited only for their actual intervals. They do not establish current state, installed freeze, cutover, certificate issuance or retirement acceptance.

## Required owner/Root follow-through

Website owner must repair R1/R2 in scoped new commits and obtain independent verification of the new exact bytes/tooling. Preserve all old negative findings and real service discrepancies. Archive CODE GO may be used only as an exact-code acceptance under its stated SDK, controlled-code/output ownership and external operating custody boundaries; it does not close any global source prerequisite.

Root must substantively close authoritative DNS/delegation/issued-and-associated destination certificate/live site/mail, source and shared ownership, actual installed full recovery/general-consumer acceptance, active dependencies, complete producer/creator shutdown, source freeze/name protection and source/root/destination/key custody. Both producer/controller lanes remain NoSourceWrites. Root must obtain fresh complete original-to-postfreeze observations and actual installation/continuity receipts, independently assess their truth, and create genuine separate committed evidence and later gates with fresh TTLs before routing authorized scoped source execution and independent global post-verification. SourceSLR, shared IAM and the separate 118-file archive remain excluded. The permanent exact-CNAME disposition, its execution and replay-safe post-verification remain independently gated.

**Review complete; SourceEligibility remains HOLD. Full migration and live retirement are not certified.**
