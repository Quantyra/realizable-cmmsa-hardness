# Conservative count reconciliation: source-only receipt

2026-09-12. S3130/S3131/S3128 under open S3126. Author `guarantee_proof_review`, delegated to this paper repository. This author is not an independent reviewer of this paper correction. No destination AGENTS.md was present at root or paper directory.

## Change and source preservation

Created `paper/submission-manuscript.md` as the editable submission source, copied from the archived root source and changed only for the count reconciliation. Root `MANUSCRIPT.md` remains byte-for-byte unchanged, SHA256 `ff00997c8c243e88982c41b0b0e24faaaafe36cec6f1903824599dc242538686`. Existing archive, tags and public state are untouched.

The current source now selects a natural P >= 1/epsilon for positive rational epsilon, with the explicit computable choice ceil(1/epsilon). It defines T = 32*(N_0+11)*P^2 and M = 2^(clog_2 T), and gives analytic log-12 threshold <= T <= M < 2T as a consequence. Since P > 0, the strict doubling bound is applicable. The constructor already supports success at least 5/6, hence 2/3; the two later references to replacing log 6 with log 12 in a least-count construction were updated accordingly. The unrelated rational-weight scale D was retained.

For each fixed L, epsilon and this P are fixed relative to the outer input. The resulting numeric list bound is explicit. Support materialization, rational arithmetic, encoded runtime, PCP and learning-transfer obligations are not certified by these count inequalities. Theorem and corollary statements are unchanged. The two weaker existing main-sampling statements (success 2/3 and failure 1/3) remain valid consequences.

The renderer reads the new source and identifies it in correspondence.json. The hardcoded count display and special inline mathematical expressions were updated. README describes the new build source and distinguishes the stale PDF/QA from current source. Generated body and crosswalk were refreshed without invoking the PDF builder.

## Formal relation and pending independent acceptance

The count source is frozen at formal-pvnp candidate `287b4e02997e94eb44572e228d8223f11ba045f4`. Author main 40350 and final Checks 7491 are successful, with 17 standard-only profiles and evaluated values 512, 2048 and 1. Final 7491 is not a failed resource-stop run. Independent count proof export/audit is still queued behind the exclusive foundation audit at this receipt; this paper correction does not presume completed three-lens acceptance. SamplingGuarantee and output-event bridge have separately reviewed finite statements, but full S3130/S3131/S3126 and encoded runtime remain open.

## Source sanity checks

`python paper/render_manuscript.py` exited zero and generated 30 displays with 128 source spans. Python AST parsing of the renderer passed. Every crosswalk source-span SHA256 and the overall source hash were independently recalculated and matched. All text preceding the changed sampling-count paragraph, including theorem/corollary statements, matches the archived source. Exact-log least-M and the later log-6-to-log-12 substitution phrases are absent from the current submission source/rendered body. The original archive hash was checked before and after edits.

Submission source SHA256: `491f54667880a85efe47fc5fd15cd371d6a945b21647a88f1acf6f748a99590b`.

No PDF build or visual QA was run. Existing PDF, QA.md and qa-receipt.json refer to the prior source and are not current approval evidence. Required next work: independent mathematical/content review of this correction, reserved-capacity PDF rebuild, crosswalk/content recheck and visual QA of that rebuilt artifact. No submission, push, publication or release occurred.
