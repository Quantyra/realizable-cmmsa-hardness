# Isolated archive HTTPS security supplement

Authorized destination-only correction for S3152/S3154/S3156/E003. No existing
migration code, historical receipt, packet or source control is modified.

```powershell
node --test scripts/aws-archive-migration/security-20261007/test.mjs
node scripts/aws-archive-migration/security-20261007/cli.mjs check
node scripts/aws-archive-migration/security-20261007/cli.mjs apply
```

`check` uses metadata reads only and writes an immutable protected check receipt.
`apply` requires authoritative PID13356/6852 absence, both active locks absent,
controller terminal phase, the exact completed full205 packet SHA256
`713abbeaeb65c456a1ba333ed0d8c77f7da8ba756085b42cd4493653ecd648ce`, all305
immutable byte pins and all45 catalog pins, and its bound bridge-removal receipt.
Pins stream through a hash without decoding dataset/catalog member contents.
No object payload, secret, key or credential value is read or printed.

Every destination S3 read/write supplies ExpectedBucketOwner063280428495.
Actual STS must be account063280428495 and IAM user ServiceAdmin. Location,
owner-only ACL, BucketOwnerEnforced, AES256, enabled versioning and all four
public blocks must pass before and after. IAM simulation checks Get/PutPolicy.
Policy must be absent or the exact owned HTTPS baseline. Temporary grants,
unrelated policies and weakened variants fail closed. Nothing deletes a policy.

Only one PutBucketPolicy SDK attempt is permitted (maxAttempts1), preceded by
an immutable intent. A lost reply is reconciled by readback; an unresolved
intent with absent policy prohibits another put. Existing exact baseline is a
conditional no-op, including restart after a lost reply. An isolated apply lock
prevents overlapping invocations; stale locks require operator investigation.
S3 provides no conditional PutBucketPolicy API: final absence readback minimizes
the race, and this procedure requires exclusive post-controller policy custody.

Protected new files live under ~/.quantyra/aws-migration-20261006/security-20261007,
with Windows inheritance removed and access granted to current user and SYSTEM.
UUID/time names and exclusive creation prevent receipt replacement. Supplements
bind the original packet hash, final policy/readback, controls, code and bridge.
The original packet and absence-based historical proof remain unchanged.

Root must independently bind this supplement and enforce its HTTPS baseline
gate in accepted evidence. `rootGate` is an isolated testable requirement, not
an edit to the existing installer/root validator or a root acceptance artifact.
No installer, active restore switch, source cleanup, source IAM mutation, GCP,
Lean, workload launch or publication occurs. Full source eligibility stays HOLD.
