# Independent all-page visual QA: parameter-proof manuscript

2026-09-13. S3128/S3137. Verdict: GO for visual/layout quality of this exact local PDF. This is not mathematical theorem acceptance, Lean certification, submission approval, or a DOI/public-release action.

## Artifact and evidence

- PDF: `output/pdf/realizable-hardness.pdf`
- SHA256: `7557d135dcec81031b37f7ae3fe6d993948fb36dcf3e5347eb7211a6956c9d69`
- Size: 634117 bytes; 17 pages.
- Source freeze: `dba95d1b9bb7b8890898b3ccdaebe386bee2cd0f`.
- Author build: reported actual session 74205, exit 0; metadata `tmp/pdfs/parameter-proof-build-20260913.json`, SHA256 `ce7a741da4bffe741b18009732682330b87d47d1f653859ab5a4613f29a61add`.
- Author rendering: reported actual session 67834, exit 0, pdftoppm, 1500-pixel page images in `tmp/pdfs/parameter-proof-pages-20260913/`.

I independently rehashed the PDF, build metadata, and all four build logs. The final log has no overfull boxes, undefined references/citations, or TeX errors. Its two bibliography underfull-box notices do not correspond to clipping or overlap in the inspected final page. Pypdf independently counted 17 pages; extracted text contains no unresolved `??` tokens. Extraction supplements, and does not replace, the visual inspection.

I read the PDF skill and directly viewed every full page image, pages 01 through 17, at the supplied resolution. I did not run a PDF/Lean compiler, change mathematical/source files, regenerate the PDF, or perform Git/public actions. I authored the independent source-integration review and contributed to the preceding parameter audit, but did not author this PDF build or its manuscript integration. This is a separate visual pass, not an independent human mathematical review.

## All-page findings

| Pages | Inspection result |
|---|---|
| 1 | Title, repository address, abstract and explicit incomplete-formalization status are legible; margins and footer are clear. |
| 2 | Theorem and learning corollary, displayed parameters and section transition are intact. The PDF uses Corollary 1 consistently through generated cross-references; this is its existing separate environment numbering. |
| 3-4 | Prior-work text and imported-contract paragraphs fit the page margins. Long headings wrap clearly; mathematical glyphs and superscripts remain readable. |
| 5 | Formula display (3.1), repeated-occurrence explanation and finite-list lemma appear without clipping; proof continuation follows normally. |
| 6 | Finite-list proof ends cleanly. Repetition discussion, Section 6 and Lemma 2 statement begin in order. The Lemma 2 proof continues naturally to page 7. |
| 7 | Exact complement proof ends with its proof symbol. Lemma 3 statement, ambient spectral bound and Chernoff display are legible. The corrected denominator 12 is visible. |
| 8 | Adaptive-history argument, assigned-witness sum over (a,c), conservative denominator cubed, marginal correction and side-condition extension all fit and retain the reviewed mathematical notation. Proof ends before the posterior section. |
| 9 | Posterior equations (6.2)-(6.7) have readable fractions, aligned multi-line displays and clear equation numbers. |
| 10 | Zoom-out equations and Section 6.1 fit. The explicit 8S global application and Delta/S threshold are visible. |
| 11 | Section 6.2 explicitly invokes the robust enlarged-ambient lemma. Transverse-table equations (6.10)-(6.11) and posterior exclusions are unclipped. |
| 12-13 | Threshold ladder and Section 7 are legible. The two-column ambient ledger breaks between rows, repeats its header on page 13, and closes with a rule. No row is cut through or overlapped. The explicit K,B ledger and A>20/kappa display (7.1) appear below it with adequate separation. |
| 14 | Completeness display (7.3), explicit-list section and product parameters are intact. |
| 15 | Natural sampling count (8.3), exception application, weight-rounding section and equations (9.1)-(9.2) fit. |
| 16 | Learning overhead, final parameter selection and concluding equations are legible with a clean final proof symbol. |
| 17 | Research disclosure and all six bibliography entries are readable. Long URLs wrap within margins; no missing glyph boxes, overlap or clipped endings appear. |

Page numbering is complete and sequential. No blank accidental page, overlapping text/equations, unresolved cross-reference marker, or visible missing-glyph artifact was found. The typography remains dense but consistent with the existing mathematical manuscript. The newly added lemmas receive resolved numbers 2 and 3; their references are readable.

## Inspected page-image identities

These hashes bind the actual images viewed; they do not substitute for PDF identity or compiler evidence.

| Page | PNG SHA256 |
|---|---|
| 1 | `04901c0d485c14731b35df133d572b07d905b222e03d4874c6f067492cf359a6` |
| 2 | `4fc68d3989b6d9ebfd2d0d81a53bc9c9133fa65fe7cf7a918fff1d9d8dc3db77` |
| 3 | `73ac9ef12f67166006f7611bd73a3236525ffdb9be1f377bc0506a7e41857384` |
| 4 | `2c5e13fdea29f623d3a2f5f03bb4901a8f3d20ce9f3eb3a87436d99229fcc31c` |
| 5 | `c524568671403994181d09f7c2d1ee28728bfb9e270ca2bee6b9198f8e4e2e8e` |
| 6 | `cc0f0d7eb77092860251ecc927a95df776d65eba2ef4fb6e74e71f45e8d40b91` |
| 7 | `c039c02bcc9e19973f71bda1a0bfeb76eb68996d72de48e3d9e73d973c07648f` |
| 8 | `3d50df117ca730d066d841478939e6b859e0c64bda62533eaf8d946d9193115d` |
| 9 | `7852f08f7f0120606c7a376022319de7c17e9b4ebe95b31ec1077f6926d30b55` |
| 10 | `53c92e7410df74c3417f85f51a1bce76c89881a6503ee2ad8b43dea7f7940b1e` |
| 11 | `0dd23decdc2b33f8432c8240bc12d8aade8d19d12fdf98ca27104f5909238a56` |
| 12 | `3ca60a3288b56258615f9305bb7f577c7b13a39c7439a3cd4ceaad34797f63af` |
| 13 | `6a73835fad0dcbdc581c4fe8e984c8967872673af389521da9364746b6116624` |
| 14 | `291286715ac5a3008400104e13cb747f4fb9380a003a48add7bbea44a44a20ed` |
| 15 | `d373514161f1313e288d9f870276ea9dc88aea97ffc17d84455377e70bd5cefd` |
| 16 | `3b592c7affd249833d436dbbfe8ecd823540a2b560d035b681967ad6725871f2` |
| 17 | `77b20debd200fca340776bc9a53c44ed16fc7397a4a9a282d5d9e8e83feb7b4f` |

## Boundary

This review applies only to the PDF hash above. The previous 15-page PDF and its older QA are historical artifacts. Any subsequent PDF change requires renewed identity and affected-page inspection. No mathematical claims were added or accepted through visual QA; the bounded source review, open formalization work, and publication decisions remain separate.
