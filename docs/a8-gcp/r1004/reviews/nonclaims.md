**Verdict: NO-GO**

Read-only non-claims review of committed head `4828b6af0f7d5946b8a08bf849d9b8ee8ef958b3`. Committed-byte SHA256 matches:

- Source: `071A4D1D34B17E065FCD7421F3C544AA00029983C75E26A231DD3E60E3FCED10`
- Checks: `31BDCB4F891A449222FC812A5447439474ECAC5F00AB22DD802B6BDB137C1078`

Scope: exactly `a8_carrier_coordinate_nested_filter`, `a8_carrier_coordinate_nested_mean`, `a8_output_coordinate_eq`, and `a8_output_pair_component_nested_mean`: coordinate/filter identities and normalized nested-mean transport, ending in one output-pair component identity.

**Blocking wording findings**

- `README.md:3–19` asserts proved NP-hardness and an established realizable strengthening. These exceed this cluster.
- `MANUSCRIPT.md:7–19`, `49–57`, `87–92`, and `777` assert the full hardness/learning results and completed proofs.
- `REVIEW.md:75–78` calls the result a hardness theorem. Historical informal-review disclosures do not supply current bounded-cluster certification.

These are existing manuscript claims, not new theorem exports. Nevertheless, they remain unqualified claim leakage on the inspected head. `README.md:45` distinguishes formal components but does not qualify the opening hardness assertions.

**Nonblocking findings**

- `docs/a8-gcp/r1004/completion-report.md:7–14` and `report.json:90–99` correctly separate compiler success, pending acceptance, story status, manuscript status, and zero replay credit.
- No affirmative P-vs-NP separation, SAT-solver, switching, Frege/PHP, or circuit-lower-bound claim found in the inspected surfaces. The hardness/completed-PCP implications above remain the boundary problem.

**Safer wording**

> This archived manuscript presents a proposed hardness argument whose full certification remains incomplete. This replay verifies four output-coordinate/nested-mean helper exports only. It does not establish complete output-Q transport, analytic A8, S3132 completion, or hardness/learning certification.

**Missing evidence links**

- Exact-head proof-adversarial and complexity verdicts: still `INCOMPLETE` at `completion-report.md:23–24`.
- Explicit helper-to-argument-step mapping.
- Pinned latest route assessment and prior accepted A9 receipt supporting the accounting assertion at `completion-report.md:14`.

**Disposition:** retain compiler evidence; withhold non-claims acceptance until the public wording boundary is corrected. If subsequently accepted through all required lenses, count **one helper-only increment**; compiler replay contributes **zero**.

| Status | Result |
|---|---|
| Compiler | Recorded GREEN under frozen-baseline policy; legacy zero-total-warning audit RED |
| Bounded cluster | Acceptance withheld; other lenses pending |
| Owning story | S3132 PARTIAL; analytic A8 OPEN |
| Full manuscript | S3137 INCOMPLETE |

No files edited; no Lean/Lake/elan executed. No route-finality asserted.
