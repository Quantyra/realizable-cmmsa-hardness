# Three-lens closeout: bounded S3132 actual-star follow-ons

Date: 2026-09-24

Accepted base: `2db30e6087b4e0546371b4874778e544d4eff4b8`

GCP evidence: `artifacts/gcp_actual_star_followons_a13_20260924T201453Z`

Archive SHA-256: `599cc05ff58d1d49081883cff5cc8c8225093c4619c0ed2dcfbd044257a9f8fd`

## Frozen sources

| File | SHA-256 |
|------|---------|
| `ActualStarLineIncidence.lean` | `14f53ed1450c6d722427a9ce4e8c4fef398084e958ff8d0ac9746c6bcd1cdccf` |
| `ActualStarLineIncidenceChecks.lean` | `450e2301574426612b2ea2c750878ca410788eb2a8dbe3677289bd029eec77fa` |
| `ActualStarKernelSupport.lean` | `113641bcfa86b2e8582cf612156953a05e29de15bce579ede9e5543b8205f4b7` |
| `ActualStarKernelSupportChecks.lean` | `f44cf537a438516549ba7f3ba037d7fd1f7cb320134440f420e4ffc89586f33d` |
| `ActualStarExtensionProduct.lean` | `d6ed23a06e1445fd8af0483a34e2a2bc8a5f9857536b704f4d5200d3ba93a131` |
| `ActualStarExtensionProductChecks.lean` | `83769a72cc2203d8bc258b2a129863eb433e27a6655add4abe10c1b6a09927d4` |

## Verification

A13 records `RESULT=PASS`, all dependency/direct/combined/replay return codes zero, source gate and forbidden-shortcut scan passing, stable direct/replay logs and `.olean` hashes, and an axiom allowlist pass for the principal printed declarations. The 66-file evidence manifest verified, the archive hash above reverified, all six current sources match their A13 copies and hashes, and the VM was independently confirmed `TERMINATED`.

## Three-lens table

| Lens | Verdict | Review / bounded note |
|------|---------|-----------------------|
| Proof-adversarial | GO-WITH-NOTES | [`2026-09-24-actual-star-followons-proof-adversarial-review.md`](../reviews/2026-09-24-actual-star-followons-proof-adversarial-review.md). No blocking defect; support is existential rather than an explicit `S = kernelSupport x`; reindexing, vector-to-line transport, union bound, and center averaging remain. |
| Complexity theory | GO-WITH-NOTES | [`2026-09-24-actual-star-followons-complexity-theory-review.md`](../reviews/2026-09-24-actual-star-followons-complexity-theory-review.md). Exact incidence, `support >= 2`, fixed-center `p^|S|`, and endpoints only; the proposed union bound, positive margin, and `mk > N` guard remain. |
| Non-claims boundary | GO-WITH-NOTES | [`2026-09-24-actual-star-followons-nonclaims-review.md`](../reviews/2026-09-24-actual-star-followons-nonclaims-review.md). No unconditional independence, bad-star bound, decoder, reduction, CMMSA, or P-vs-NP claim; axiom printouts are not repository-wide. |

## Accepted wording

Proved exact quotient-line incidence for a uniform actual leaf extension; existence of a supported nonzero zero-sum relation from a nonzero joint-kernel witness; and fixed-center supported-line cylinder probabilities, including empty-support and zero-increment endpoints. A13 records GCP build/replay success for these six files. Full CMMSA certification remains incomplete.
