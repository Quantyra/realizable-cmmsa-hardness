# Immutable review evidence supplement

This supplement preserves the source lifecycle and source production repair reviews for AWS migration/source retirement (S3152/S3156/E003). Both original indexes and every original receipt remain unchanged. Historical NO-GO findings and development failures remain evidence; live eligibility stays HOLD.

All 261 original in-scope files are committed as exact raw blobs. New scoped .gitattributes files disable text conversion for these receipts without changing root attributes or ignore rules. The six parent report/dispatch snapshots preserve their current exact bytes inside the owning satellite; original parent files are untouched. manifest.json explicitly retains historical CLI summary pin exceptions.

The 12 indexed synthetic fixture trees under tmp/slr and tmp/spr contain committed-evidence histories essential to reproducing the reviews. synthetic-fixtures.tar.gz contains every working file and embedded .git file, including indexes, objects, refs and reflogs, with exact payload hashes. Raw fixtures remain in their original locations. The bundle represents them as ordinary evidence, without adding submodules or changing fixture Git repositories. File ownership, modes and timestamps in the archive are normalized for deterministic reconstruction; original content bytes and Git history are preserved.

Run the standalone local verifier with Node:

```powershell
node docs/aws-migration-2026-10-06/source-production-repair-review/commit-preservation/verify-preservation.mjs
```

It checks original receipt files against the immutable manifest, verifies all archived member hashes and checks the current original fixture trees without mutating them. --commit COMMIT additionally checks original receipt blobs in Git. To restore elsewhere, extract the bundle only into a new empty directory; member paths retain tmp/slr and tmp/spr. Do not extract over the preserved originals. Reproduction of production probes is outside this evidence-only dispatch.

Secret inspection covered 1182 evidence/fixture files and 369 inflated loose Git objects; all 24 credential literal matches are synthetic, with no unresolved high-signal secret candidates. No real credentials, archive decryption keys or remote payloads were read. No suites, builds, research, cloud calls, push, publication or parent commit are part of this work.
