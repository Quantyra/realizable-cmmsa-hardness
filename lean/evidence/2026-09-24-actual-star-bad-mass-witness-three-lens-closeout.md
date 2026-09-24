# Three-lens closeout: bounded S3132 B2 witness bridge

Date: 2026-09-24

Accepted base: `456b99bde65c3a748a3d75bfe4de60d08ed91144`

GCP evidence: `artifacts/gcp_actual_star_bad_mass_witness_b2_20260924T205749Z`

Archive SHA-256: `c38947fa5ff54f8792ce9dd126ef57cfa2ceeb9bcb411f4ced6520cf3c7761a5`

| File | SHA-256 |
|------|---------|
| `ActualStarBadMassWitness.lean` | `d2eeba320ddf2ee01f6c06a4295d717bc40fc011b22c1244a9fc5cd51f8de2f5` |
| `ActualStarBadMassWitnessChecks.lean` | `403d6f9b149f8467d20d45cd80e6c87a1b3dfadb9260df58c0bfdac27011d4b1` |

## Verification

B2 records `RESULT=PASS`. All 34 evidence-manifest entries rehash successfully; the archive and frozen source hashes match; dependency, direct, combined, and replay return codes are zero; source, shortcut, axiom, replay-log, and `.olean` stability gates pass. The final VM status is `TERMINATED`.

## Three-lens table

| Lens | Verdict | Review / bounded note |
|------|---------|-----------------------|
| Proof-adversarial | GO-WITH-NOTES | [`2026-09-24-actual-star-bad-mass-witness-proof-adversarial-review.md`](../reviews/2026-09-24-actual-star-bad-mass-witness-proof-adversarial-review.md). Full joint failure reaches an exact nonzero relation and same-center line event; `hsum` is unused by the mass equation and the witness may depend on the tuple. |
| Complexity theory | GO-WITH-NOTES | [`2026-09-24-actual-star-bad-mass-witness-complexity-theory-review.md`](../reviews/2026-09-24-actual-star-bad-mass-witness-complexity-theory-review.md). Credits the bounded bridge and each specified fixed-center event mass only; numerical instantiation and the global estimate remain open. |
| Non-claims boundary | GO-WITH-NOTES | [`2026-09-24-actual-star-bad-mass-witness-nonclaims-review.md`](../reviews/2026-09-24-actual-star-bad-mass-witness-nonclaims-review.md). No unconditional independence, center average, good margin, decoder, reduction, or full CMMSA claim; `hk >= 1` excludes the zero-increment endpoint. |

## Accepted closeout

B2 proves that failure of joint directness yields a supported line event, and computes the mass of each specified fixed-center line event. The support-stratified bad-star bound remains open.
