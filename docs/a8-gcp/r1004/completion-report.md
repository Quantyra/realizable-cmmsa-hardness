# Immutable analytic A8 compiler/evidence replay

Run `cmmsa_a8_output_20261004T223605Z_d74b7c51`. Destination `Quantyra/realizable-cmmsa-hardness`, branch `main`. No input changes, proof repairs, local Lean/Lake/elan, restart, warning suppression, or successor theorem.

| Status | Result |
|---|---|
| Compiler attempt | GREEN: dependency/source/Checks/fresh axiom native exits `0/0/0/0` |
| Bounded increment | ACCEPTED WITH NOTES as one helper-only A8 cluster; replay and review retries give zero helper/roadmap credit |
| Owning story | S3132 PARTIAL; analytic A8 remains OPEN |
| Full manuscript certification | S3137 INCOMPLETE |

Zero errors, zero unsolved goals. All four principal exports have exactly `propext`, `Classical.choice`, `Quot.sound`. Warning headers by stage: 968/968/968/1; zero owned headers, zero inherited-baseline regression against frozen union of 981. The broader legacy warning-token count is 3274; its zero-total-warning audit remains RED, unchanged, as S3137 debt. No warning cleanup was attempted.

The exports are `a8_carrier_coordinate_nested_filter`, `a8_carrier_coordinate_nested_mean`, `a8_output_coordinate_eq`, and `a8_output_pair_component_nested_mean`. They form one output-coordinate/nested-mean helper cluster feeding analytic A8. They are not `a8_output_q_le_actual_predecessor_sum`, do not cover the complete output-pair sum, and do not close analytic A8. The three lenses accept this as the first A8 helper-only cluster since the latest route assessment, not four increments. Analytic A9 remains the prior accepted manuscript-facing increment; the three-helper threshold is not crossed. Compilation/replay and review retries earn zero new helper or roadmap credit.

Source SHA256 `071A4D1D34B17E065FCD7421F3C544AA00029983C75E26A231DD3E60E3FCED10`; Checks SHA256 `31BDCB4F891A449222FC812A5447439474ECAC5F00AB22DD802B6BDB137C1078`. Exact project closure: 199 modules. Captured dependency baselines: 11574 package sources and 2520 core sources. Source/configuration/compiler/package/object hashes, commands, native exits, stdout/stderr, and axiom profiles are retained in the capture and verified cloud archive.

Archive first downloaded to `C:\a8gcp\d74b7c51.tar.gz`, verified at `2026-10-04T22:48:43+00:00`, then copied to `C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness\docs\a8-gcp\r1004\runs\cmmsa_a8_output_20261004T223605Z_d74b7c51\cmmsa_a8_output_20261004T223605Z_d74b7c51-evidence.tar.gz` (178 characters). Both custody hashes and remote SHA256 are `32EDBC62B771DC534FDA1767B3C075E24245136CD577B66C384211E8149EE279`. Presence and both hashes verified before the finally-style stop command. The independent terminal receipt verifies instance `8337954477286097405`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`, VM `quantyra-lean-builder-01` TERMINATED. Exactly one start occurred. Inherited tracked dirt/deletions and untracked Lean hashes/status remained unchanged; other inherited untracked contents were outside the write scope.

| Review lens | Result |
|---|---|
| Compiler/audit | GREEN under frozen-baseline policy; legacy zero-total RED retained |
| Proof-adversarial | GO-WITH-NOTES; no HIGH theorem defect; acceptance retains captured-closure limitation |
| Complexity | GO-WITH-NOTES; coordinate/component transport only; analytic A8 remains open |
| Non-claims | GO-WITH-NOTES after bounded S3128/S3137 wording correction; initial NO-GO and correction are preserved |

See `report.json`, `three-lens-closeout.md`, `reviews/`, `runs/cmmsa_a8_output_20261004T223605Z_d74b7c51/prospective-audit.json`, unchanged `audit.json`, `custody.json`, `terminal.json`, and independent terminal receipt. The failed read-only setup observation and shutdown-time SSH observation are retained; neither affected the authoritative compiler or custody gates.
