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

## Current regeneration status

The count-reconciled submission source, `body.tex`, correspondence manifest,
and PDF have now been regenerated and independently visually reviewed.
Current PDF: 15 pages; see `count-reconciliation-pdf-qa-2026-09-12.md` and
its JSON receipt for exact hashes, all-page review, and the two harmless
bibliography underfull-box notices. The bounded mathematical/source correction
review is `count-reconciliation-independent-review-2026-09-12.md`.

`QA.md` and `qa-receipt.json` remain historical records for the earlier
14-page PDF; they do not certify this revised artifact. Complete Lean
formalization, manuscript-wide final reconciliation, and submission approval
remain open. This local rebuild is not a new public release.


## Parameter-proof source candidate (2026-09-13)

The private submission source now includes the reviewed exact complement
query identity, robust eight-times-threshold local application and its
counted proof, explicit ambient bounds, and A-before-h parameter order.
The renderer preserves these reviewed LaTeX blocks directly from the
canonical Markdown and records their source spans. Body and correspondence
are regenerated for independent source review; no PDF rebuild is included
in this increment.

The previously verified 15-page PDF (SHA256 beginning `9c2ddd`) and its
prior QA receipts remain historical artifacts. That PDF is stale relative
to this source candidate until a new authorized build and all-page QA.
Published MANUSCRIPT.md, DOI records, releases and Lean artifacts are
unchanged. This candidate does not claim complete formal certification.
