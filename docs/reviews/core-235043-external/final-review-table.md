# External conditional-core reviews

Pinned Main26A2011F and ChecksCF8E6397, native run235043. Full goal remains open.

| Provider/model | Proof | Complexity | Non-claims | Coverage |
|---|---|---|---|---|
| Claude Opus5.5[1m], actual modelUsage | GO-WITH-NOTES | GO-WITH-NOTES | GO-WITH-NOTES | Full Main3659lines, contracts/numerics/rowgeneric; imported proofs partly statements only; no hash computation by reviewer |
| AGY Gemini3.1ProHigh, actual init + report attestation | GO | GO | GO | All3exports complete explicitly attested;71866-byte critical source packet; imported numerics/combinatorics/append proofbodies excluded |

Claude retains five MEDIUM notes: HC46/Spectral47 inhabitance/vacuity exposure, selector applicability, enlarged fixedT/P, ambientJ/encoding scale. These remain full-goal obligations. Earlier Gemini5 is INCOMPLETE due truncation, superseded only for corrected focused coverage. No global completion or unconditional hardness claim.
