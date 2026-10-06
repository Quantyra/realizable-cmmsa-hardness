# Native receipt storage review - 2026-10-06

Review complete. No receipt/source bytes, paths, or historical manifests were changed; no upload, move or deletion was performed.

## Corrected disk measurement

The prior 177.25 GiB figure summed file names and counted hard-linked libraries repeatedly. The tree has 2,951,922 file paths but only 81,918 distinct file identities. Distinct allocated file data is 3.8912 GiB, of which 3.2506 GiB has links outside this tree. Only 0.6406 GiB of file-data allocation could be released by removing all names inside this tree while outside links survive. This is not a safe deletion allowance. Directory/index/MFT metadata, disk compression semantics, concurrent writes, and future link changes can affect Windows free-space results. Enumeration and identity checks returned no errors or changed/missing files.

NTFS enumeration used file IDs and allocation sizes, with real file-stat link counts for distinct identities; representative file IDs were independently checked against Python os.stat. The source helper uses os.link, and samples had 52 or 92 links. Do not upload repeated libraries as independent objects or advertise 177 GiB of recoverable storage.

## Disposition

| Data | Decision | Space / rationale |
|---|---|---|
| 840 byte-exact .tar/.tar.gz/.tgz/.zip archives | Eligible for private S3 archival after reference and restore gates; initially retain local | 0.4133 GiB logical archive bytes; 839 distinct SHA256 hashes. Archive structure and ZIP CRC checks passed; no unsafe member paths found. Not every archive is a final accepted proof receipt. |
| Completed-run command records, stdout/stderr, source identities, reviews | Preserve as historical evidence; optionally archive with their run bundle | These distinguish failed/interrupted runs from accepted results. Do not infer acceptance from filenames. |
| Source snapshots / custody records / audit manifests / reviewer ledgers | Keep local | Hash-pinned and referenced by verification and recovery workflows; small compared with apparent library overlays. |
| Runtime lib overlays and compiled object identities | Keep required paths and shared files; no bulk purge | Repeated hard links dominate apparent size. Compiler/verification code uses LEAN_PATH and absolute object/hash pins; deleting only receipt aliases mostly frees no file data. Rebuilding is not automatically equivalent to preserving historical byte pins. |
| One duplicate archive pair | Consolidation candidate only with both names preserved | Two byte-identical, independently allocated 56,463-byte files. Replacing one with a verified same-volume hard link could save about 56 KB; deleting its pathname is not approved. |
| __pycache__ / .pyc | Disposable-cache candidate after no-active-writer check | Negligible savings. No unique research evidence or hash-pinned binaries belong in this class. No caches were removed. |

## References and integrity

`archive-catalog.json` records every archive's original relative path, original absolute path, size and independently computed SHA256, plus a proposed content-addressed S3 key and duplicate aliases. Destination/version fields are null because no S3 upload happened. `reference-baseline.json` checked 148,047 unique absolute paths across 149,736 occurrences in receipt JSON files <=2 MiB outside library/cache folders. It found 599 already-missing unique targets (77 library paths, 6 log paths, 516 other paths). These were present before this review and must not be attributed to migration. Larger JSON, computed Python paths, relative paths, external repositories and every binary consumer are outside this static JSON audit; inspected scripts and Quantyra review documents also contain relative/dynamic references.

Examples needing preservation: docs/a7-certification-20261003/verify-rebuild.py reads runtime-prebuild/local-native-own414 and cached_manifest/source_custody paths, verifies object hashes and constructs LEAN_PATH. audit_material_claims.py expects a particular durable-run evidence archive at its existing local path and SHA256. Three independent review documents and Quantyra research records cite durable-runs and source snapshots. Never replace expected archive/object bytes with a Markdown or JSON pointer at that same filename; those scripts will fail.

## S3 execution gates

1. Establish the authorized research AWS account, private bucket, region, retention policy and credentials. Default AWS CLI authentication is absent; do not borrow service-specific cyint-ea credentials for research storage.
2. Freeze a bounded, closed run. Rehash after packaging and before upload; exclude currently dirty/changing artifacts. Include original path/hash/alias maps and dependencies. Store one payload per digest; retain each path's restore mapping.
3. Upload with private access and encryption. Preserve the returned object version and actual URI in the catalog; verify uploaded content with an independent download and SHA256 comparison. Do not use an S3 ETag as proof of SHA256 equality.
4. Rehydrate an isolated copy to the original expected paths, or use a reviewed resolver before historical verification. Validate path containment and restore aliases. Re-run relevant bounded receipt consistency checks without modifying historical evidence or making new proof claims.
5. Repeat reference audit and compare against the recorded baseline: no additional missing references. Keep manifest/source/custody and review pointers available locally. Evict only individually verified, archived, unused local files; do not recursively delete this tree or shared dependency stores.
6. Measure real Windows free space after any eventual eviction. Preserve fail/interrupt provenance, byte hashes and nonclaim boundaries.

## Recommendation

Retain this tree locally for now: only ~656 MiB of file data is exclusive and most of it is evidence. Archive completed bundles to S3 for durability when research credentials and a bucket are established, not as a major disk-recovery measure. The reviewed archive catalog is ready for that bounded follow-up. No evidence deletion is recommended now. Reassess other disk areas using hard-link-aware allocation measurements rather than recursive Length totals.

## Operational notes

The receipt repository already had tracked/untracked research changes and deleted source-snapshot paths at intake; none were staged or repaired by this review. Three abandoned temporary inventory files created by this review total 629,568,750 bytes; execution policy rejected removal with no reason supplied. They remain in the user's Temp folder, separate from research evidence: native-receipts-inventory-20261006.jsonl, native-receipts-identity-inventory-20261006.jsonl, native-receipts-inode-inventory-20261006.jsonl. The completed compressed path map is also in Temp (91,517,192 bytes); it is not committed as a giant repeated-path Git artifact. The durable catalog, baseline and summary are the compact review artifacts.
