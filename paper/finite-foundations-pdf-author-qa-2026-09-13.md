# Combined finite-foundations PDF author QA - 2026-09-13

Verdict: PASS for build and visual layout only. This is author QA, not independent mathematical review, human peer review or Lean certification.

The frozen source commit is `4a6d6a141b62d16b10b806549dedc4a5813a89a7`. All four source files remain byte-identical to that commit after the existing `python paper/build.py` workflow. Actual build session 31703 returned exit 0; render session 76132 returned exit 0. The PDF-operation marker succeeded exactly once for this batch, before PDF authoring.

The output is `output/pdf/realizable-hardness.pdf`, SHA256 `d1ab2f17ccf7f602150912d68522524a14a87dabbc350b54beade3febe6df6bc`, 717759 bytes, 21 Letter pages. All 21 rendered pages were individually inspected at 1500-pixel maximum dimension. The finite matrix-lift, spectral-character and inverse proofs have readable symbols and fitting displays; the parameter ledger, page transitions and references show no clipping, overlap, black squares or broken table layout. No layout or mathematical edits were needed.

The final LaTeX pass has no overfull boxes or unresolved references. Two bibliography underfull-box notices remain, without visible layout defects. The separate independent all-page review is `paper/finite-foundations-independent-visual-qa-2026-09-13.md`, SHA256 `8a7d79c118e3667c67b877b5bb37b053cc575cf13840a8818c86cda11c9f2fec`.

The prior 17-page PDF (`7557d135dcec81031b37f7ae3fe6d993948fb36dcf3e5347eb7211a6956c9d69`) and its QA were preserved in ignored `tmp/pdfs/history-before-finite-foundations-20260913/`; earlier history remains intact. Build logs and all 21 PNGs are retained under `tmp/pdfs/`. The build metadata still says visual QA pending because it is an immutable pre-QA record; this report records completion.

The paired JSON binds every page image, four raw logs, build metadata, source pins, independent note and historical-preservation record. JSON SHA256: `68a4cadc94a35662b2883dd9f9dd524f1b40169ca454dbabd5107799f1533ac2`.

No published MANUSCRIPT, DOI or release was changed. No Lean artifacts were copied or compiled. Global hypercontractivity and other named external inputs remain imported; the full formalization remains incomplete. The root subsequently authorized local archiving of this PDF and its QA after review. This archive authorization is limited to layout/document evidence and does not authorize publication or formal proof acceptance. The JSON's four source pins describe the build-time snapshot; the README alone received later status and conditional-consolidation documentation, without changing the mathematical source or PDF.
