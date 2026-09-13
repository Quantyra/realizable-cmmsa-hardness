# Editorial disposition review after manuscript reconciliation

2026-09-13. S3128/S3137. Reviewer: compact_source_encoding_audit. **GO for this exact editorial revision.** The four editorial findings are addressed for proceeding to the separately authorized PDF build and visual QA. This does not close the full Lean goal, certify every upstream proof, approve publication or assert current PDF acceptance.

## Exact candidate

Baseline: a8d9363ecbd86ef44ccb2a7ae47cb2ad1df8a40f. I read the full canonical-source, renderer, bibliography and paper-local README diff and checked the generated artifacts read-only.

- `paper/submission-manuscript.md`: SHA256 `dc749b0ef184e5d0792c3d366b2461c4478add9facbd4d653627731adc4db240`, 105252 bytes.
- `paper/body.tex`: SHA256 `2ce0589f440c091033a8013c5db1eef0a07651309755c69caa185ec45972c97f`, 113685 bytes.
- `paper/correspondence.json`: SHA256 `94d01334ca0718cb0c223caa9583ad629c4f2b6f6eae548361cafdf99fa5294f`, 22387 bytes.
- `paper/render_manuscript.py`: SHA256 `58511f1b7f0eee07cd8e04bff09a4b2af4ef440f268dcdf3fab0f9881b11b06d`, 17280 bytes.
- `paper/references.bib`: SHA256 `92d3773c80c1fa51594a40008d4a27cc211a73beb407220cc14668567f93dfc8`, 1619 bytes.
- `paper/README.md`: SHA256 `171fe5434cefcf6fce4005f5e7c0a077bef1bd73f35f990f472cdb5ce6ae2f54`, 10929 bytes.

## Findings and disposition

The four import-status replacements correctly distinguish the historical scoped source decoder at threshold S from the robust 8S enlarged-ambient application actually proved here. Original contract 3, including its S threshold and side-condition statement, is unchanged. The prose does not claim that the source S-threshold theorem was reproved. Outer hardness, star/clique transport, counting, covering, compilation and learning retain their explicit imported status.

The canonical ../SOURCES.md and ../REVIEW.md links now resolve to existing root companions. The sole renderer change normalizes these two forms before the existing citation/disclosure substitutions. The ordered list of rendered citation commands and keys is identical to the baseline body; the repair has not lost HN/Hir22 or MZ/MZ24/BKM citations.

The canonical header identifies a local submission draft based on archived version 0.1.0. The paper README marks the old 21-page PDF as prior evidence and adds the current submission provenance and content-review links, with PDF QA pending and complete Lean verification incomplete. Its statement that the historical content review did not itself review this later revision is accurate; this separate note supplies that disposition. No root publication document or DOI metadata changed in the diff.

The bibliography removes exactly the six UTF-8 bytes c3 af c2 bb c2 bf before the initial @misc. Every subsequent byte is identical to baseline: no entry, author, version, date, title, URL or key changed.

The only change inside any of the four complete raw-LaTeX blocks is the approved plain subsection heading 'The dual-norm level bridge and the Boolean conclusion'. A whole-block comparison after that single literal replacement verifies every proof formula, inequality, definition and argument is unchanged. All legacy indented mathematical displays also compare exactly. The complete canonical diff contains no other mathematical edit. This includes the original contract 3 at S, robust 8S application, inverse constants and all appendix inequalities.

All 130 source-span hashes and the manifest source hash were checked against the current canonical file. All four complete raw blocks occur in the body under the existing Gaussian-binomial formatting substitution. These inspect the actual generated artifacts without running the renderer. The author-reported regeneration is consistent with the checked artifacts; no old-PDF equivalence is inferred.

An initial read-only verification invocation stopped at Python parsing before executing due to a malformed temporary heading-string literal. The corrected invocation above completed all assertions; it did not mutate sources or generate artifacts. This was a verifier invocation repair, not a manuscript or proof repair.

## Scope

The content reconciliation SHA a16b3f653f522c00c06a479017acf1a6ec5de14bf3f44a4c52d2aa638b94e7fa remains immutable and binds its earlier candidate. This note records subsequent dispositions instead of retroactively changing its source identity. My prior mathematical contributions and review roles remain disclosed there and in the upper-chain review. No manuscript/generated edits, PDF or Lean compiler, Git operation, public action or new proof expansion occurred. Only this requested note was written. Final current-PDF all-page QA remains outstanding.
