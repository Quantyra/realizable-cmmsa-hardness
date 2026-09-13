ï»¿# Submission paper build

This is the local submission-paper preparation increment (S3128 under S3126).
It has not been submitted, announced or released. The complete Lean
formalization remains incomplete; the paper claims no formal certification.

## Sources and output

- `realizable-hardness.tex`: article preamble, title and bibliography setup.
- `submission-manuscript.md`: editable submission source, forked from the preserved
  root `MANUSCRIPT.md`; incorporates the conservative natural sample count.
- `body.tex`: complete typeset manuscript body, generated from
  `paper/submission-manuscript.md` by `render_manuscript.py`.
- `references.bib`: primary-source bibliography for the imported results.
- `correspondence.json`: source-line spans and hashes for the transcription.
- `../output/pdf/realizable-hardness.pdf`: rendered local paper.

The root `MANUSCRIPT.md` and published v0.1.0 archive remain unchanged.
The editable submission Markdown is the current mathematical build source.
The renderer contains explicit LaTeX for every one of its 30 displays and
retains every prose paragraph and table. Theorem 1 remains Theorem 1;
the source's Corollary 2 is Corollary 1 in the LaTeX environment's separate
counter. Cross-references use LaTeX labels. The finite-list repair is
presented as Lemma 1 with an explicit proof environment. The end of the
main composition marks completion of Theorem 1 and Corollary 1.
The sample-count reconciliation replaces the exact-log least-count constructor
with a conservative natural constructor; the theorem statements remain unchanged.
See `count-reconciliation-2026-09-12.md` for scope and pending independent review.
The transcription still requires independent content review before submission.

## Reproduce

Install Python 3 and a LaTeX distribution with `pdflatex` and `bibtex`.
The document uses `article`, AMS math/theorem packages, `geometry`,
`booktabs`, `longtable`, `microtype`, `url` and `hyperref`.
From the repository root run:

```text
python paper/build.py
```

The builder regenerates the body/correspondence manifest, runs pdfLaTeX,
BibTeX, then two resolving pdfLaTeX passes, and copies the completed PDF
to `output/pdf/`. It fixes the source-date environment and suppresses PDF
creation dates, trailer IDs and source path metadata. Exact binary identity
is asserted only for the tested toolchain recorded in the QA receipt;
other TeX versions can change typography or bytes. Auxiliary files, pass
logs and page renders live in ignored `tmp/pdfs/`.

For visual verification with Poppler:

```text
pdftoppm -scale-to 1400 -png output/pdf/realizable-hardness.pdf tmp/pdfs/page
```

## Style reference

The actual released A001 article was inspected, not its historical notebook:
[Jacobian-Weyl canonical TeX](https://github.com/Quantyra/jacobian-weyl-quantum-phase-space/blob/v0.3.9-referee-revision/docs/notes/A001-arxiv.tex)
and the [PDF-first reference preprint](https://doi.org/10.5281/zenodo.21864761).
Its single-column 11-point article layout, one-inch margins, Computer Modern,
AMS theorem/proof environments, conventional title block, numbered equations,
linked bibliography and explicit coverage boundary inform this paper.
Only typography/structure is borrowed; corporate authorship remains
Quantyra Research and none of A001's mathematical or Lean claims is imported.

## Submission issues remaining

The full Lean proof and its audit are incomplete. An independent content
and visual review of this exact paper candidate is required before calling
it submission-ready. No venue, submission category, author identity changes,
submission authorization or public-announcement destination is selected by
this local increment. Existing v0.1.0 archive and both historical tags remain
unchanged; the existing DOI identifies that archive, not this later PDF.

## Historical count-reconciled regeneration status

The count-reconciled submission source, `body.tex`, correspondence manifest,
and PDF have now been regenerated and independently visually reviewed.
That prior PDF: 15 pages; see `count-reconciliation-pdf-qa-2026-09-12.md` and
its JSON receipt for exact hashes, all-page review, and the two harmless
bibliography underfull-box notices. The bounded mathematical/source correction
review is `count-reconciliation-independent-review-2026-09-12.md`.

`QA.md` and `qa-receipt.json` remain historical records for the earlier
14-page PDF; they do not certify this revised artifact. Complete Lean
formalization, manuscript-wide final reconciliation, and submission approval
remain open. This local rebuild is not a new public release.


## Current reviewed parameter-proof PDF (2026-09-13)

The private submission source includes the reviewed exact complement
query identity, robust eight-times-threshold local application and its
counted proof, explicit ambient bounds, and A-before-h parameter order.
The renderer preserves the reviewed LaTeX blocks directly from the
canonical Markdown and records their source spans. Source commit
`dba95d1b9bb7b8890898b3ccdaebe386bee2cd0f` passed bounded independent
source review.

The current local PDF has **17 pages**, SHA256
`7557d135dcec81031b37f7ae3fe6d993948fb36dcf3e5347eb7211a6956c9d69`.
It was rebuilt with the existing workflow and all pages passed author
and independent visual inspection. See
`parameter-proof-pdf-author-qa-2026-09-13.md`, its paired JSON, and
`parameter-proof-independent-visual-qa-2026-09-13.md`. The final build
has no overfull boxes or unresolved references; two bibliography
underfull-box notices caused no observed visual defect.

The prior verified 15-page PDF (SHA256 beginning `9c2ddd`) and its QA
receipts remain historical artifacts. A byte-preserved copy is retained
under ignored `tmp/pdfs/history-before-parameter-proof-20260913/`.
Published MANUSCRIPT.md, DOI records, releases and Lean artifacts are
unchanged. This is a privately reviewed paper candidate, not a new
release, submission approval or complete formal certification. The full
Lean goal remains incomplete.
