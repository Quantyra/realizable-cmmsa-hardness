# Provenance of migrated Lean sources

- Source repository: `C:\Users\Dan\Desktop\Projects\formal-pvnp` (GitHub `Quantyra/formal-pvnp`)
- Source commit: `e8eb955ebfd22c58397c52cc7e203e8ecbc362f1`
- Source tree: `certifications/realizable-hardness/{lean,lakefile.toml,lean-toolchain,lake-manifest.json}`
- Copy method: `git archive` of that commit (tracked files only)
- Destination: this repository, alongside the manuscript
- Excluded: `.lake`, oleans, `temp/`, `formal-pvnp` research history unrelated to this paper, secrets

## Certified GO / GO-WITH-NOTES increments included

These increments have three-lens GO or GO-WITH-NOTES in `reviews/` (2026-09-15 and 2026-09-16). Supporting Lake modules they import are included so the tree compiles, even when a supporting file is not itself a three-lens headline.

Headline certified pack (not exhaustive of every supporting file):

| Increment | Source prove commit | Three-lens |
|---|---|---|
| Presentation descent | `2018a4d` | GO-WITH-NOTES |
| Center restriction | `f54f116` | GO-WITH-NOTES |
| Representative sampler | `4702d23` | GO-WITH-NOTES |
| Rejection union | `37dae51` | GO-WITH-NOTES |
| Star acceptance | `5606cd9` | GO-WITH-NOTES |
| Source-star completeness | `c574bd9` | GO-WITH-NOTES |
| Source-star soundness | `f35269d` | GO-WITH-NOTES |
| CMMSA randomized reduction | `c058348` | GO-WITH-NOTES |
| Theorem 1 from maps (conditional) | `10c3b9b` | GO-WITH-NOTES |
| Headline parameters | `605b07e` | GO-WITH-NOTES |
| SAT→3SAT source | `1488ff8` | GO-WITH-NOTES |
| Selected coin ruler | `38d9ad0` | GO-WITH-NOTES |
| Packed `Tree.parse` (`treeParseTag`) | `52b57f2` | GO / GO-WITH-NOTES |
| Packed `gcdBits` | `7105c95` | GO-WITH-NOTES |
| Packed `readRatTag` | `dbdca87` | GO-WITH-NOTES |
| `readRatTag_of_tree` | `93d3513` | GO-WITH-NOTES (local cert after GCP reauth failure) |
| Packed `readFormulaTag` | `41c6e1c` | GO-WITH-NOTES (local cert after GCP reauth failure) |

Later stop-loss packings on the same tree, not separately three-lens’d at copy time: `readSignedTag`, `readListTag`, `readFormulaTag_of_pair`, `readRowTag`, `readRowListTag`, `readParametersTag`, `readTableTag_mem_FP`, `listLenBits`. They are present because they are on `e8eb955`.

## What is not claimed

Unconditional manuscript Theorem 1, Corollary 2, inhabited `hSrcCmmsa`, `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, P versus NP, publication, or DOI/release change.
