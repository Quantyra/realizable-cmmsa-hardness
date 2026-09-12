ï»¿# Submission paper build

This is the local submission-paper preparation increment (S3128 under S3126).
It has not been submitted, announced or released. The complete Lean
formalization remains incomplete; the paper claims no formal certification.

## Sources and output

- `realizable-hardness.tex`: article preamble, title and bibliography setup.
- `body.tex`: complete typeset manuscript body, generated from the unchanged
  root `MANUSCRIPT.md` by `render_manuscript.py`.
- `references.bib`: primary-source bibliography for the imported results.
- `correspondence.json`: source-line spans and hashes for the transcription.
- `../output/pdf/realizable-hardness.pdf`: rendered local paper.

The frozen root Markdown remains the mathematical source of this increment.
The renderer contains explicit LaTeX for every one of its 30 displays and
retains every prose paragraph and table. Theorem 1 remains Theorem 1;
the source's Corollary 2 is Corollary 1 in the LaTeX environment's separate
counter. Cross-references use LaTeX labels. The finite-list repair is
presented as Lemma 1 with an explicit proof environment. The end of the
main composition marks completion of Theorem 1 and Corollary 1.
These are presentation changes; no numerical or theorem extension is intended.
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
