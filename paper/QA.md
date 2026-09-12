# Paper preparation verification

The local paper preserves the frozen Markdown source and presents its complete
argument in a conventional article. This receipt records authoring-agent checks;
it is not a human peer review or a Lean/kernel certification. The complete Lean
formalization remains incomplete. Independent content and visual review is a
separate gate before submission readiness.

## Correspondence checklist

All 11 numbered source sections, the abstract, three subsections, 30 mathematical
displays, and every nonheading prose/table/list source span are included.
`correspondence.json` records the 127 source spans and their hashes. Source
headings, blank lines and the original title/version header are accounted for
separately. The section correspondence is one-to-one:

| Source/paper section | Included content |
|---|---|
| 1 | Problem and reduction definitions, main theorem, exact learning corollary |
| 2 | Earlier realizable hardness, nearlinear contribution, limits of attribution |
| 3 | Notation and all seven imported theorem contracts |
| 4 | Explicit-list exception construction, guarantees and full proof |
| 5 | Reason for changing the repetition parameters |
| 6, including 6.1â€“6.3 | Posterior, rank, zoom-out, transversality and threshold ladder |
| 7 | Loss ledger, outer contradiction and completeness parameter order |
| 8 | Sampling and explicit realizable-list reduction |
| 9 | Rational-weight rounding and learning transfer |
| 10 | Fixed-parameter asymptotic choice and final gap parameters |
| 11 | AI development/review disclosure and lack of formal/human certification |

Presentation changes include mathematical typesetting; numbered equations and
cross-references; a separate corollary counter (source Corollary 2 becomes
Corollary 1); the explicit finite-list lemma statement and proof environment;
the local submission-draft status; and conventional bibliography citations.
The lemma's added conclusion restates the guarantees already proved in the
source, including the L+1 leaf bound. No substantive mathematical extension is
intended. The source itself already says the collision loss is bounded above.
The mapping is a coverage aid, not an automatic mathematical-equivalence proof.

## Build and visual checks

The tested toolchain is Python 3.14, MiKTeX-pdfTeX 4.24 (MiKTeX 26.1), BibTeX,
and Poppler 24.04.0. Two consecutive final builds produced identical PDF bytes.
The final TeX log has no overfull boxes, undefined references/citations or
LaTeX warnings. All 14 final pages were rendered with Poppler at a 1200-pixel
maximum dimension and inspected by the authoring AI. Title, numbered statements,
all displays, table, bibliography, page breaks and margins were checked. No
clipping, overlap or missing glyphs were observed. The independent reviewer
identified and the author corrected a posterior-subscript transcription and
an implicit lemma conclusion before this receipt.

`qa-receipt.json` pins the source/build/output hashes and coverage result.
Generated auxiliary files and page PNGs remain ignored under `tmp/pdfs/`;
the delivered PDF is under `output/pdf/`. No existing public file or historical
tag was modified. No push, publication, announcement or submission is performed
by this local increment.
