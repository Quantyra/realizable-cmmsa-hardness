# GCP build receipts

These are the curated builder receipts for the realizable-CMMSA Lean route.
A `RESULT=PASS` line covers only the scope printed in that run's `OUTCOME.txt`.
This directory does not assemble Theorem 1 or Corollary 2.

`satellite/` was copied from this repository's local `artifacts/` directory.
`prior/` was copied from `realizable-cmmsa-hardness-artifacts` on the same machine.
`INDEX.tsv` gives the SHA-256 of every copied file.

Included for every run: outcome files, `EVIDENCE.sha256` manifests, axiom,
shortcut, source, replay, and build logs, and hash sidecars. Included for a
PASS run only when the sealed archive was still on disk: that `.tar.gz`.
Sixteen sealed PASS archives are in this tree. Their bytes match the archive
hashes recorded for B10, B37, B48, B49g, B50al, B50am_r1, and B50ap.

Left on the local disk, and not published here: git-history bundles, `.olean`
files, Lean sources already in this repository, shell launchers, input
payloads, and the tarballs of failed runs.

Some accepted runs no longer have a sealed tarball locally. Their extracted
logs are here, and the archive SHA-256 cited for them in the planning notes
cannot be recomputed from this directory. That set includes fixed-center
first-moment B19, numerical closure B21, scalar closure B27, and fixed-rho
dimension guard B29, plus the older retained-law and retained-agreement
receipts in `prior/`.

Hash sidecars may still name `/home/dfredriksen_quantyra_org/`. They contain
no credentials.
