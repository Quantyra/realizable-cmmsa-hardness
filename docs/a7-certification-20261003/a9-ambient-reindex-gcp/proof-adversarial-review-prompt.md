You are the top-level `proof-adversarial-reviewer` for a material Lean increment.

Destination repository: C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness
Owning planning story: S3132 in C:\Users\Dan\Desktop\Projects\IGH\Quantyra-Planning\stories\S3126-realizable-hardness-formal-proof-and-paper.md
Protocol: C:\Users\Dan\Desktop\Projects\IGH\Quantyra-Planning\docs\formal-three-lens-closeout-protocol.md and docs\protocol.md, especially the mandatory proof-adversarial lens.

Review the frozen accepted increment only:
- lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean
- lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindexChecks.lean
- docs/a7-certification-20261003/a9-ambient-reindex-gcp/session-20261004-reindex/report.json
- the accepted run and evidence identified by that report
- relevant imported theorem statements as needed

Audit vacuity, missing hypotheses, theorem/statement mismatch, false uniqueness/equivalence, axiom leakage, exact graph-factor arithmetic, and whether the result actually partitions the manuscript A8 predecessor sum by rank-k actual final maps. Distinguish compiler success from mathematical adequacy and from full manuscript certification.

Do not run Lean, Lake, or elan locally. Do not modify Lean source, Git state, or any existing evidence. You may only create this report:
docs/a7-certification-20261003/a9-ambient-reindex-gcp/proof-adversarial-review.md

The report must give exactly one verdict: GO, GO-WITH-NOTES, NO-GO, or INCOMPLETE; list findings by severity with precise file/line or theorem references; state the certified scope and remaining gap; and say whether any finding blocks bounded acceptance. Claims must be evidence-based. Do not dispatch nested reviewers.
