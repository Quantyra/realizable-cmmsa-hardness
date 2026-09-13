# Submission paper build

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
The bounded source integrations and manuscript-wide content reconciliation have
local agent reviews. These do not certify all imported proofs or complete Lean
formalization; final submission identity and venue decisions remain separate.

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

The full Lean proof and its audit are incomplete. The current 31-page PDF
has completed author and independent all-page visual QA.
The manuscript-wide content reconciliation and its editorial disposition have
local agent reviews, bounded to their stated scope. No venue, submission category, author identity changes,
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


## Prior reviewed parameter-proof PDF (2026-09-13)

The private submission source includes the reviewed exact complement
query identity, robust eight-times-threshold local application and its
counted proof, explicit ambient bounds, and A-before-h parameter order.
The renderer preserves the reviewed LaTeX blocks directly from the
canonical Markdown and records their source spans. Source commit
`dba95d1b9bb7b8890898b3ccdaebe386bee2cd0f` passed bounded independent
source review.

That historical reviewed local PDF has **17 pages**, SHA256
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


## Prior reviewed finite-foundations PDF (2026-09-13)

The canonical submission source now includes a separately reviewed inverse
derivation with an explicit two-thirds cutoff, dyadic moments, joint-label
gluing, affine selection and full-signal error absorption. A finite matrix-lift lemma now proves the zero-on-deficiency affine
restriction bridge, including dependent constraints, the target orbit,
constant full-rank fibres and exact-budget averaging. A finite-character
spectral lemma now supplies the actual extension, averaged-injection and
translation laws, restricted adjoint, exact eigenvalue and squared-norm
identity. The inverse still uses its existing weaker spectral estimate
and conservative budgets. Global hypercontractivity remains an external
input. The reviewed mathematical source is frozen at
`4a6d6a141b62d16b10b806549dedc4a5813a89a7`.

That prior local PDF has **21 pages**, SHA256
`d1ab2f17ccf7f602150912d68522524a14a87dabbc350b54beade3febe6df6bc`.
Build session 31703 and render session 76132 both returned actual exit 0.
All 21 pages passed author and independent visual QA; see
`finite-foundations-pdf-author-qa-2026-09-13.md`, its paired JSON, and
`finite-foundations-independent-visual-qa-2026-09-13.md`. The final build
has no overfull boxes or unresolved references; two bibliography underfull
notices caused no visible defect. The source/body/correspondence remain
unchanged by this layout archive; this README records the later status.

The prior 17-page PDF7557d135 and its QA are historical, with byte-preserved
copies under ignored `tmp/pdfs/history-before-finite-foundations-20260913/`.
Published MANUSCRIPT.md, DOI records and Lean artifacts remain unchanged.
This is a local layout/document archive, not formal proof acceptance,
submission approval or public release. Full formal certification is incomplete.

## Conditional Lean consolidation handoff

User instruction recorded on 2026-09-13: once the Lean proof for this paper
is finalized, consolidate it in this paper repository,
`C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness`.
Until the full paper proof is finalized, `C:/Users/Dan/Desktop/Projects/formal-pvnp`
remains the active proof surface. No migration is performed by this record.

The future handoff must include the paper-specific Lean sources, exact
dependency pins, theorem-to-paper crosswalk, verification and audit records,
and reproducible build instructions. Transfer only the paper-specific proof
and its required dependencies, not the whole general research library.
Verify the consolidated proof in a clean fresh checkout before treating
consolidation as complete. This conditional handoff does not change proof
claims or authorize publication, push, submission or release.


## Current hypercontractivity submission candidate (2026-09-13)

The complete finite binary hypercontractivity appendix and its inverse-lemma
application were integrated and source-reviewed at commit
`a8d9363ecbd86ef44ccb2a7ae47cb2ad1df8a40f`. See the local
[lower-chain review](hypercontractivity-lower-chain-independent-review-2026-09-13.md)
and [upper-chain review](hypercontractivity-upper-chain-independent-review-2026-09-13.md).
They assess the reconstructed finite mathematics and the exact transcription;
they do not claim Lean verification or certify all unchanged upstream inputs.

The subsequent editorial revision distinguishes the source decoder's original
S-threshold contract from the robust 8S application proved in this submission,
repairs relative source/review links and bibliography-prefix bytes, and gives
the appendix heading a plain PDF bookmark. Its canonical heading identifies a
local submission draft based on archived version 0.1.0, not a new released version.
The cited outer hardness, star/clique transport, maximal-pair counting,
compilation and learning contracts remain imported.

The root REVIEW.md and MANUSCRIPT.md describe the preserved archive; the local
reports above concern this later submission source. The local
[manuscript-wide content reconciliation](hypercontractivity-manuscript-content-reconciliation-2026-09-13.md)
found no new mathematical consistency issue and identified the editorial fixes
above. It binds the source at a8d9363; the subsequent
[editorial disposition review](hypercontractivity-editorial-disposition-review-2026-09-13.md)
accepted the exact editorial revision. Intentionally cited upstream proofs are
not recertified by these passes. The final local PDF has **31 pages**, SHA256
`f4e7552ccd31f4a4457d2604f0285960daf9eadd51c31decc6152e09c5872746`.
Build session 35326 and render session 33887 returned actual exit 0. All 31 pages
passed [author visual QA](hypercontractivity-pdf-author-qa-2026-09-13.md);
[Independent visual QA](hypercontractivity-independent-visual-qa-2026-09-13.md)
also passed for this exact PDF; the reviewer inspected all 31 pages separately. The prior 21-page PDF and
its logs are preserved under ignored
`tmp/pdfs/history-before-hypercontractivity-20260913/`.
No public release, submission authorization, DOI change or completed Lean proof
is implied. The conditional paper-specific Lean consolidation handoff above
still applies only after full proof finalization.
