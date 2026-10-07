# Independent source lifecycle production review

2026-10-07. Independent adversarial reviewer, native Codex CLI. Parent work: AWS migration and source retirement (S3152/S3156/E003). Dispatch: `source-lifecycle-production-review-dispatch.txt`. Primary audit workspace: `C:/Users/dfred/Desktop/Projects/realizable-cmmsa-hardness`. Website implementation was inspected read-only.

**CODE NO-GO for both production integrations. LIVE ELIGIBILITY HOLD.** Both contain real, conditionally reachable execution paths and safe local defaults. Their passing author suites do not cover the defects reproduced below. This review authorizes no live alias release, freeze installation, deletion, revocation, DNS cleanup or migration-completion claim.

| Integration | Exact reviewed source commit | Code verdict | Live eligibility |
| --- | --- | --- | --- |
| Archive source retirement | `12a58220884586e42149acc6844821b64ff07536` | NO-GO: endpoint provenance and replacement-bucket protection | HOLD |
| Website source lifecycle | `39c629bc151f734d07c64330c13f64a84d9e104c` | NO-GO: physical-send/terminal expiry, closing source observations, unversioned deletion permissions, committed evidence provenance, incomplete IAM validation | HOLD |

Archive checkout HEAD is `7eaf68a621352a19dfe9b81d7cb53ed8d9d4f748`, a later, disjoint logical-hardlink consumer repair. All 34 files in `scripts/aws-archive-migration/source-retirement/` match Git blobs in the reviewed `12a5822` commit. All 18 files in website `scripts/aws-migration/source-lifecycle/` match `39c629b`, also its observed HEAD. Before/after hashes confirm neither reviewed source directory changed during this audit. This does not review or accept the logical-hardlink repair.

## Scope and evidence custody

Both implementations pin source profile `cyint-ea-prod`, account `485386182336`, principal `arn:aws:iam::485386182336:user/cyint-ea`; destination profile `quantyra`, account `063280428495`, principal `arn:aws:iam::063280428495:user/ServiceAdmin`.

Archive scope is exactly `quantyra-research-archive-485386182336-us-east-1` to `quantyra-research-archive-063280428495-us-east-1`: 205 immutable source/destination version mappings, 18,579,936,167 bytes, 105 encrypted chunks, 44 recovery catalogs and 45 catalog pins including the core catalog. The separate shared CYINT 118-file archive candidate, Braket buckets/secrets/source roles and other users/roles are outside these runners' allowlists. None of the code's 205-version coverage establishes global ownership completeness.

Website scope is `quantyra-website`, 112 original null-version objects, CloudFront `E1YKX9P25CCTN8`, and source ACM `arn:aws:acm:us-east-1:485386182336:certificate/d0b6eecb-bd1c-437d-a82f-fadf99895aa7`. Destination scope is bucket `quantyra-website-063280428495-us-east-1`, distribution `EFNS26JKDEMJO` / `d29u4d35k2uyay.cloudfront.net`, ACM `arn:aws:acm:us-east-1:063280428495:certificate/ed72ab8f-f839-49d4-a75a-d1d5081e1472`, and Route53 zone `Z0765812BNRBG5KQGYTU`, for `quantyra.org` and `www.quantyra.org`, in `us-east-1`.

Audit evidence, runnable probes and retained synthetic fixtures are indexed at:

`C:/Users/dfred/Desktop/Projects/realizable-cmmsa-hardness/docs/aws-migration-2026-10-06/source-lifecycle-review/evidence-index.json`

`fixture-hashes.json` provides exact fixture file paths, sizes and SHA-256 hashes. `before.json`, `after-prescribed.json` and `evidence-validation.json` record source identities, current Git status, committed-byte comparisons and historical receipt validation. The only parent writes are this designated report and the separate CLI final. Original reports, source files, historical receipts and inherited retry/capture dirt were preserved. There were zero real AWS requests/mutations, source repository Git writes, remote payload/key/secret retrievals, research executions or publications. Synthetic Git writes occurred only inside isolated test repositories, as required to test committed evidence loading.

## Findings

### A1 — HIGH: archive reads and mutations accept ambient custom endpoints

`aws.py:18` constructs the mutation client without `ignore_configured_endpoint_urls=True`; its guard checks SDK version, attempt count and `_needs_retry`, but no endpoint. `AWS.__init__` and `AWS.client` likewise leave read endpoints configurable.

With the installed boto3/botocore `1.43.108`, setting `AWS_ENDPOINT_URL_S3=https://archive-fixture.invalid` caused the real Mutator to issue one signed DeleteObject to that host, with its fixed bucket, owner, version and ETag. The destination observation client selected the same custom host. All credentials were synthetic and sockets forbidden. Results: `independent-archive-results.json`, scenarios `A1-custom-mutation-endpoint-accepted` and `A1-custom-observation-endpoint-accepted`.

A service-specific S3 override can leave STS/IAM on ordinary AWS endpoints while replacing source freeze, inventory and destination custody observations. ExpectedBucketOwner is a request field, not independent authentication of an arbitrary server. A fake server can supply plausible metadata/absence responses without touching the real bucket; real credentials could also be sent to an unintended endpoint. AWS documents this environment/profile endpoint behavior and the client setting that suppresses it. [AWS service-specific endpoints](https://docs.aws.amazon.com/sdkref/latest/guide/feature-ss-endpoints.html).

Required repair: suppress ambient global/service/profile endpoint overrides for every production read and mutation client, validate production endpoint/partition/region/TLS assumptions, and test that overrides cannot replace authenticated observations or redirect a mutation. Preserve explicit fake transport injection solely for tests. The website implementation already suppresses configured endpoint URLs.

### A2 — HIGH: an empty replacement before archive bucket intent can be deleted

Archive `inventory.configuration:74` reads 18 configurations but no ListBuckets creation marker or comparable bucket-continuity witness. `adapter._state:40` returns namespace rows only. `retirement.state:112` rejects bucket reappearance only once a bucket intent exists.

After all 205 version confirmations, a newly created empty bucket of the same name/account with matching configuration is indistinguishable from the original emptied bucket. The runner accepts it, appends its first bucket intent and deletes the replacement.

`independent-archive-recreated.py` reproduced this through the real immutable RootLoader, ProductionAdapter, journal and installed SDK. It retained all 205 prior version confirmations, exposed a changed creation marker through the fake ListBuckets API and substituted an empty source bucket with matching controls. The runner made zero creation-marker reads, sent one DeleteBucket and returned successful source absence. Existing tests correctly reject replacement **after** bucket intent; they do not close this earlier window. The replacement fixture models custody failure; no real recreation or deletion occurred.

Exact retained fixture: `C:/Users/dfred/Desktop/Projects/realizable-cmmsa-hardness/tmp/slr/archive-recreated-1hynnrwa`. Synthetic evidence commit `2a489b05b2e41959aa47014067b24633a67e3563`; separate gate commit `948dc62216632802577858ceb9811013a2bb23c8`; gate SHA-256 `a733b50d36b839ec11d203a4bf9a75e420f8549cbbe0d808a6c0d9314537a04d`; journal SHA-256 `f5cd950eabe7ed11c4a9fbd99da5d9c30b085dacde385f7d9f46fd4c66bf2e65`.

Required repair: bind original-to-postfreeze bucket continuity and compare current drift markers before empty-bucket intent/send, with independently accepted creator shutdown/name protection. CreationDate is a useful drift marker, not an immutable instance ID: AWS documents that policy edits can change it. Do not invent an immutable identifier or silently adopt a changed marker. [AWS bucket metadata](https://docs.aws.amazon.com/AmazonS3/latest/API/API_Bucket.html).

### W1 — HIGH required-path gap: website root evidence and gate commits are unenforced

`packet.loadPacket:76` reads gate, baseline, acceptances and receipts from the filesystem. `currentCommit` checks only the website code HEAD. No root evidence commit, committed root allowlist or separate later gate commit is required or read.

The real loader accepted an entirely uncommitted packet in a temporary directory without a Git repository. `independent-website-results.json`, scenario `W1-uncommitted-packet-accepted`, records its path and gate hash. Byte hashes and repeated revalidation are useful and credited; externally supplied approved hashes remain an explicit trust boundary. This finding does **not** claim that merely creating a local packet fabricates genuine out-of-band root approval. It establishes that the dispatch's required immutable, separately committed root evidence/gate provenance path is absent.

Required repair: read exact root evidence blobs from an explicit immutable parent commit, bind a root-owned exact allowlist/baseline and underlying receipts, then read matching gate bytes from a distinct later gate commit. Check those bindings at every authorization without creating a circular gate/evidence hash requirement. The archive loader provides this separate-commit approach.

### W2 — HIGH: website gate expiry is not checked at physical send

`lifecycle.adapterFor:47` verifies the packet before calling `aws.mutateOnce`. The real SDK then performs asynchronous serialization/signing/middleware work. `wire.mjs:11` checks only the active-send flag and physical request count; it has no bound gate/TTL authorization callback. Its finalizeRequest middleware also only counts attempts.

The production adapter and installed SDK reached a fake physical mutation handler while packet verification at that handler already rejected the expired gate. The initial probe advances time during synthetic credential resolution. A second probe first resolves and checks both identities through productionAWS's real STS transport, confirms the source signer resolves only once, then advances the clock at the actual mutation transport handoff. The missing TTL check persists with the shared signer already resolved. Results: `independent-website-results.json` and `independent-wire-expiry-results.json`.

The refined fixture is deterministic fault injection for latency between the last adapter check and HTTP dispatch, not a claim that the production credential provider normally rotates or remains unresolved. Single-send/retry protection works; it does not enforce authorization expiry. Required repair: propagate the bound authorization callback into the final SDK/HTTP send guard and reject expiry or changed bound bytes after signing and immediately before each physical request. Retest warmed credentials and delayed middleware/transport preparation.

### W3 — HIGH: final website journal append can expire before success returns

`core.Lifecycle.attempt:149` authorizes before appending/fsyncing the final `observed` row, then returns without another authorization. The reconciliation return at lines 117–118 has the same structure.

The independent certificate-retirement probe completed its final journal append, advanced the clock beyond the gate expiry and received `observed`; packet verification on return rejected the gate. It made exactly one synthetic mutation. This is the actual destructive certificate path with a valid packet, durable Journal and isolated observations. Result: `W3-success-returned-after-terminal-expiry`.

Required repair: recheck the current root gate, all bound evidence TTLs and bytes after final durable append, after lock-release work where material, and immediately before returning CLI success. Preserve terminal evidence on expiry and require root reconciliation; a written terminal row must not itself imply accepted completion.

### W4 — HIGH: closing website observations can report stale source absence

`collector.observe:87` captures source bucket state; line 93 captures source certificate state. After potentially long DNS/live HTTPS sweeps, the closing block rechecks source CloudFront, target CloudFront/certificate and target versions, but neither source bucket/current namespace nor source certificate. Line 159 assigns a new `observedAt` timestamp to the entire result.

Two independent production-collector fixtures recreated the source bucket or source certificate during the live proof sweep. Both completed normally and still returned the relevant source absence flag as true. Results: `W4-stale-source-bucket-absence` and `W4-stale-source-certificate-absence`. Thus a destructive-step postcondition or DNS owner handoff can be accepted using absence observed before the final dependency phase. These scenarios deliberately model unexpected source drift despite claimed custody.

Required repair: finish slow dependencies first, then freshly verify all relevant source resource absence, whole source/current/history/delete-marker/upload namespaces, destination exact versions/data/controls and configurations. Compare full closing observations and retain their actual intervals. Do not give early source reads a fresh completion timestamp. Distributed observation still requires custody through independent post-verification; the repair need not pretend to be atomic.

### W5 — MEDIUM: website IAM simulation discards denied/incomplete resource results

`collector.simulate:74` validates the action-level EvalActionName/EvalResourceName and missing context, then returns EvalDecision. It does not inspect ResourceSpecificResults, their exact coverage, decisions or missing context.

An action-level `allowed` row with an exact resource-level `explicitDeny` and missing `s3:VersionId` context returned `allowed`. Result: `W5-denied-resource-result-accepted`. This is an inconsistent/deficient response fault injection; it is not evidence that AWS normally returns contradictory decisions. The requested fail-closed validation is missing. The archive simulator rejected the equivalent fixture.

Required repair: validate the actual requested action/resource/context, explicit complete pagination, exact resource results and consistency of all decisions. Preserve the exact literal-null VersionId context and bucket-level cleanup simulation. [AWS IAM simulation](https://docs.aws.amazon.com/IAM/latest/APIReference/API_SimulatePrincipalPolicy.html), [resource-specific results](https://docs.aws.amazon.com/IAM/latest/APIReference/API_ResourceSpecificResult.html).

### W6 — HIGH: website freeze/preflight does not support current unversioned deletion semantics

The committed source preflight has `GetBucketVersioning: {}`; the source is unversioned. `policy.freezePolicy:13` explicitly denies `s3:DeleteObject` via NotAction while permitting exact-principal null `s3:DeleteObjectVersion`. The wire sends `DeleteObject?versionId=null`; `collector.simulate` evaluates only `s3:DeleteObjectVersion` for that API call. The proposed-policy test even expects `s3:DeleteObject` denial.

Current AWS documentation specifically warns against sending version IDs to unversioned buckets and states that an explicit bucket-policy deny of either deletion permission makes unversioned deletion fail with 403. The general versioned-action mapping does not supersede this unversioned-bucket rule. [AWS object deletion guide](https://docs.aws.amazon.com/AmazonS3/latest/userguide/DeletingObjects.html), [DeleteObject API](https://docs.aws.amazon.com/AmazonS3/latest/API/API_DeleteObject.html), [S3 permission matrix](https://docs.aws.amazon.com/AmazonS3/latest/userguide/using-with-s3-policy-actions.html).

The independent probe verified the actual unversioned baseline, exact deny statement and version-only IAM request. Result: `W6-unversioned-delete-permission-mismatch`. No live DeleteObject was attempted, so this finding is a documented service-contract mismatch, not a measured production 403. Mock responses that always permit the version action cannot establish a usable real cleanup path. Alias release/hosting deletion could precede the later blocked object cleanup.

Required repair: choose an owner-reviewed cleanup/freeze design compatible with the actual bucket versioning state and AWS-supported conditions, simulate every effective required permission, and verify the service behavior in an authorized disposable fixture before accepting the production contract. Do not invent `s3:VersionId` support for actions that do not document it, weaken write denial broadly, or silently change the source versioning state under this review.

## Credited controls and verification

The default archive CLI performed a zero-request offline full205 check. Its disabled execute gate rejects before AWS session construction. Website's default lifecycle check is local; tests verified disabled/absent gates reject before invoking the AWS factory. Both integrations have conditional real CLI/adapter/kernel execution under accepted synthetic inputs; neither is an unconditional refusal skeleton.

Archive root loading binds the original stored allowlist hash, fixed parent allowlist path, explicit committed evidence blobs, separate committed gate bytes, code pins, exact accounts/resources, eight acceptance kinds and twelve concrete production proof types. It checks full metadata/hash reuse, policy readback, producer topology and shutdown leases, local PID absence using safe Windows process-query APIs, destination key/retention custody, installed consumer outputs, ownership, dependencies and global website acceptance. Root must independently assess actual external receipts; schemas do not prove their truth. New disjoint HEAD movement does not weaken reviewed source-byte pins.

Archive mutation guard checks gate/code/TTL at actual botocore before-send, disables endpoint retry/redirect handling and uses one SDK attempt. Installed URLlib3Session.send source still explicitly disables urllib3 retries. Independent expiry injection made zero physical sends; resource-level IAM denial was rejected. Its durable locked/fsynced chain, exact version/ETag/owner requests, ambiguous-intent readback, no blind retry, post-intent recreated-bucket rejection, closing namespace relists and post-terminal expiry checks are credited. A1/A2 remain despite those controls.

Website separates alias release from destructive retirement; release leaves source Enabled=true. It requires extra live custom-domain, mail/consumer/archive/control and shutdown evidence for retirement. Its full original namespace/mapping, streamed destination hashes, metadata/tags/encryption checks, shared resolved signer, exact null version/owner/ETag serialization, source CF ETags, destination association, producer/control receipts, installed freeze/name guard checks and journal renewal/prefix/ambiguity rules are substantive. Its physical request and middleware counters prohibit retries for timeout/503/redirect fixtures. W1–W6 remain despite those controls.

| Independent prescribed verification | Final result |
| --- | --- |
| Archive safety suite | 45/45 pass |
| Archive actual SDK transport suite | 2/2 pass, including 18 operation/error/redirect subcases |
| Archive production integration suite | 21/21 pass after fixture-path rerun |
| Website safety/integration suites | 26/26 pass after fixture-path rerun |
| Archive original proof binder, `--verify-only` | All 305 original artifacts and 45 catalogs pass; 205 exact mappings/byte total pass |
| Additional independent probes | 15 checks pass: 9 website checks, 5 archive SDK/refusal checks, 1 archive replacement-bucket execution probe |

The first retained run used a long temporary path under the historical evidence directory name. Archive integration failed during synthetic committed-proof lookup; website CLI refused HistoricalJournalDestinationForbidden, producing 25/26. A sequential rerun used workspace `tmp/slr` and process-only `core.longpaths=true`: archive 21/21 in 442.709 seconds, website 26/26 in 31.117 seconds. No repository/global Git configuration was written. Original failure logs and final passing logs are both retained; failures were not relabeled as passes. `prescribed-results.json` and `prescribed-rerun-results.json` record commands, intervals, exit codes and hashes.

Additional probes use forbidden sockets, synthetic credentials, injected SDK HTTP handlers and locally cached public website fixture bytes. The archive replacement probe isolates bulk local hashing while exercising the real root loader/adapter/kernel/SDK; the real full305/45 binder runs separately. Synthetic execution is not production execution or actual installed-consumer acceptance. Both early-expired website packets and archive wire-expired authorizations were correctly refused by the negative controls.

Local manifest verification matched all 33 archive completion artifact entries and all 10 website completion evidence entries. Runtime was Node `v26.5.1`, boto3/botocore `1.43.108`, website AWS SDK `3.1147.0`. Installed Python SDK function hashes match `completion-sdk-inspection.json`. Detailed runtime/source/receipt pins are in `evidence-validation.json`.

Original archive packet SHA-256 remains `713abbeaeb65c456a1ba333ed0d8c77f7da8ba756085b42cd4493653ecd648ce`; HTTPS supplement `ba9a2880792fc6f1e59ca5bdd95ac4d76276638ddeef747fdb1e814a07914a65`; stored allowlist `5856b4c5b62173c5e4fb0f7a3e24299d75414fa2365d3b1d14cd05f0768c2ea8`; canonical allowlist `3b8b27c6e8fe088bffdc1f19609b19097e283ef245a904fa14e1cdabb492373d`. Website tooling hash remains `81805ed0bb0d740fe73c26b07c98e0e300b8c56c8feb8e674bebe3c0b10e9a73`; original source manifest `724fb7349cae1dff0ec55308dbd953b3fb4c941c8b0c181ae96ee5a59dd822a0`.

Historical live read receipts are credited only for their recorded intervals. Archive's source was not frozen; neither proposal was installed. Website's completion preflight records 112/112 data parity and 116 allowed simulations while the destination certificate remained PENDING_VALIDATION. Those observations do not establish present state, postfreeze proof, or resolve W6. No historical success flag was promoted to current eligibility.

## Live eligibility and owner handoff

Current parent status retains unresolved complete authoritative DNS inventory/delegation/cutover/TLS/site/mail proofs, source ownership/shared archive118 and Braket source-role attribution, shutdown of all producers/creators, installed effective freezes, destination retention/key/root override custody, active dependencies and actual installed recovery/general-restore acceptance. The 93-byte installed core restore acceptance remains bounded and valid; recovery hardlink repair `7eaf68a` is committed but its owning report explicitly leaves independent review, new root acceptance, installation and actual PowerShell recovery validation pending. Do not treat dry runs or its synthetic tests as that runtime proof.

Historical source ACM DNS cleanup remains a separate S3157 obligation. Website `dns-disposition` emits a disabled exact-record owner handoff; it implements no Route53 DELETE. The operating document explicitly leaves the durable hash-pinned retirement overlay and exact deletion/post-verification to S3157. No installed import/plan/stage replay-suppression overlay was established by this audit. Root must require that owner implementation/proof before deleting the exact old source validation CNAME, preserve historical exports and destination validation records, and prove later staging cannot recreate retired records. W4 also applies to the freshness of the disposition's source-absence evidence.

IAM simulation is read-only and may differ from live authorization; it is not atomic permission or data custody. Bucket policies cannot prevent the owning account root from replacing them; actual independent root change-hold/creator control must remain effective throughout execution and post-verification. [AWS simulator limits](https://docs.aws.amazon.com/IAM/latest/APIReference/API_SimulatePrincipalPolicy.html), [S3 root policy override](https://docs.aws.amazon.com/AmazonS3/latest/API/API_PutBucketPolicy.html). Do not invent a new executor, revoke shared CYINT identities, expand these resource allowlists, or weaken genuine ownership/DNS holds to make a schema pass.

Remaining to-do list for source retirement (S3156): owning satellites repair A1/A2 and W1–W6 in scoped new commits; rerun relevant suites and independent adversarial checks on the exact new bytes; root substantively close the existing DNS/ownership/consumer/custody/shutdown prerequisites; create fresh, separately committed root evidence and gate windows; only then route already-authorized scoped execution and independent global post-verification, including the separate DNS replay-suppression/deletion path. This audit is complete; the migration and live source retirement are not complete. Reports and audit artifacts are intentionally uncommitted under the dispatch's no-Git-write boundary.
