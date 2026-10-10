# Independent visual and source-to-PDF content review: *Realizable Nearlinear-Gap Hardness for Small Monotone Formulas* (31 pp.)

**Verdict:** All 31 pages are readable and nothing is clipped, but the PDF does not yet match the source closely enough to accept. Six transcription defects need fixing and re-rendering. There is no overall GO.

**What I had to work with:** For every page I had the rendered image and its extracted text. I also had all the source files listed in the request. I used no tools, so a few things were not checked:
- **SHA-256 values:** I did not recompute any of them, so none are confirmed.
- **Build logs:** I did not open them. Apart from the eight bibliography notices, I relied only on what is visible on the page.
- **Text comparison:** I compared the PDF with the source by reading, not by an automated diff.
- **Fine detail:** checks like hairline overlaps are only as good as the page-image resolution allows.

**Skipped pages: none.**

---

## 1. Page-by-page coverage

Finding IDs (T = transcription, V = visual, B = bibliography, C = claims) are explained in §2.

| Pg | What's on the page | Visual result | What I found |
|---|---|---|---|
| 1 | Title, abstract, keywords, Status, §1 start | OK | **T-1**: the word "a" in "less than a γ fraction" is set as a math variable. V-1: minus signs printed as hyphens ("1-ϵ"); "ϵ=0" is half in math, half in text |
| 2 | Theorem 1, eq. (1.1), learning model, Corollary 1, eq. (1.2), §2 | OK | **T-2**: (1.1) ends with "." but the source has ","; the sentence continues with "such that". T-9: the source calls it Corollary 2, the PDF calls it Corollary 1 (consistent inside the PDF) |
| 3 | Rest of §2, §3 notation, contract 1 | OK | **T-3**: the pinpoint "Definitions 1.2/1.7, Theorems 1.3/1.8, Section 7" is lost; only "[3, 2]." remains. **T-4**: the text says "Contract 3", but the PDF's contracts have no numbers. V-2: citations placed after the sentence's full stop ("version. [3, 2].") |
| 4 | Contracts 2–5 | OK | T-5: "label" set in math italic ("label transport", "queried label"). T-6: "dimensions a,c": a upright, c italic |
| 5 | Contracts 5–7, eq. (3.1), Lemma 1 statement | OK | T-4 again ("contract 3" has no visible target); (3.1) renders cleanly |
| 6 | Lemma 1 conclusion and proof, §5, start of §6 | OK | **T-7**: the conclusion paragraph of Lemma 1 was written by the renderer and is not in the source |
| 7 | Lemma 2, start of Lemma 3 | OK | The text layer drops the bar on K̄ (affects copy/search, not the printed page) |
| 8 | Lemma 3 proof, Lemma 4 statement | OK | Matches body.tex |
| 9 | Lemma 4 proof | OK | **MZ24 A.13 sentence matches the source word for word** (see §3) |
| 10 | Lemma 5 statement and proof | OK | Matches |
| 11 | End of Lemma 5 | OK | Matches |
| 12 | Lemma 6 | OK | The F_n and E display fits in the margins |
| 13 | End of Lemma 6, (6.1)–(6.4) | OK | "Bin" set in italic (minor) |
| 14 | (6.5)–(6.8) | OK | T-1: "the probability a uniform d-subspace", where "a" is set as a variable |
| 15 | (6.9), §6.1, start of §6.2 | OK | **T-8**: "P′(good Q)" prints as "P′(goodQ)" in math italic, losing the space. T-5: "leaf-label". "2hm(ξ−1000ρ)": hm printed upright |
| 16 | (6.10)–(6.12), §6.3 | OK | Clean break between pages 15 and 16 at the (6.10) display |
| 17 | End of §6.3, §7, table | OK | The table has no overflow, and "zoom-/outs" breaks at its hyphen. T-1: "at most a factor 2^r" |
| 18 | K, B; (7.1)–(7.3); start of §8 | OK | **T-6**: "Choose an integer A before h": A printed upright |
| 19 | (8.1)–(8.3) | OK | T-1: "may enlarge a common denominator" |
| 20 | End of §8, §9 (9.1)–(9.3), §10 (10.1) | OK | Matches |
| 21 | (10.2), (10.3), §11, start of Appendix A, footnote | OK | **T-2**: (10.3) ends with "." and then "where…" follows. Footnote URLs are complete |
| 22 | Theorem 2, A.1, (A1)–(A2) | OK | Matches body.tex |
| 23 | (A3), A.2 (W6), A.3 (DR6) | OK | Small block matrix renders correctly |
| 24 | (A4), (A5) | OK | Multi-line summation limits under (A5) are clean |
| 25 | A.4: (T1), (A6), (T2) | OK | Matches |
| 26 | (A7)–(A9) | OK | The two-line (A8) display fits |
| 27 | (A10)–(A14) | OK | Matches |
| 28 | (A15)–(A17) | OK | Matches |
| 29 | (A18)–(A21) | OK | Matches |
| 30 | A.7: (A22), (A23), proof of Theorem 2 | OK | Matches |
| 31 | Closing remark, bibliography [1]–[8] | Readable | B-1, B-2, B-3 (see §2) |

On every page I found no missing or replacement glyphs, no clipping, no overlaps and no broken references ("??"). Equation numbers 1.1–10.3 and A1–A23 are all present and in order.

## 2. Findings that need action

**Transcription (source → PDF)**
- **T-1: the article "a" set as a variable.** Seen on pp. 1, 14, 17 and 19. The cause is the renderer's rule for single letters. (The "probability a" on p. 18 really is a variable, but it reuses the letter a, which already means advice dimension. That clash is in the source itself.)
- **T-2: punctuation changed at displays (1.1) and (10.3).** The source has commas; the PDF has full stops before text that continues the sentence.
- **T-3: pinpoint citation lost.** The source's "[HN, Definitions 1.2/1.7, Theorems 1.3/1.8, Section 7; Hir22]" becomes just "[3, 2]". This is real content loss. (The MZ/MZ24/BKM and OpenAI citations convert without loss.)
- **T-4: references to unnumbered contracts.** The source numbers the contracts 1–7. The PDF shows each as an unnumbered "Imported contract." heading, yet pp. 3 and 5 still say "Contract 3" and "contract 3".
- **T-5, T-6, T-8: wrong typeface.** "label" in italic, "a,c" in mixed styles, "A" upright on p. 18, and "goodQ" run together.
- **T-7: text the renderer adds that is not in the source.** The Lemma 1 conclusion paragraph, the closing sentence of §3 ("Lemma 1 gives… Sections 6–10…"), the Keywords and Status lines, and the changed final sentence ("This completes the proofs of Theorem 1 and Corollary 1. □"). The content is consistent with the source. But correspondence.json maps source lines only, so these additions, including one mathematical statement, have no recorded origin. The correspondence map is also coarse: lines 338–857 and 1362–2107 are each recorded as a single span.
- **T-9: theorem numbering differs.** The source's "Corollary 2" is "Corollary 1" in the PDF. It is consistent inside the PDF, but cross-checking against the source has to account for it.

**Visual**
- **V-1:** Minus signs printed as hyphens, and operators placed outside math mode, throughout the prose ("1-β", "3J-2D", "C-2^{-10h²}"). Readable, but not publication typography.
- **V-2:** Citations placed after the sentence's full stop in §2.

**Bibliography (p. 31)**
- **B-1: the eight underfull-line notices.** These match what is visible: all eight entries have stretched first lines with wide word gaps, e.g. [2], [5], [7] and [8] ("OpenAI.␣␣The Unique Games Theorem.␣␣…"). Nothing overflows, is clipped or is lost. The notices are cosmetic and can stay as they are. Setting the bibliography ragged-right would remove them.
- **B-2: proper nouns lowercased.** "grassmann graphs" [4] and "pessiland" [3], because the BibTeX titles are not braced.
- **B-3: year printed twice.** "28 October 2025, 2025", "23 June 2026, 2026", "13 May 2026, 2026" and "23 September 2026, 2026", because both `howpublished` and `year` print.
- **Confirmed correct:** the snapshot hash adc7f124…bf78a matches in the .bib and the PDF. The OpenAI, arXiv, ECCC, DOI and ToC URLs are complete, and the long ones break only at allowed points.

## 3. Claims boundary

- **MZ24 A.13 attribution (p. 9):** the PDF matches the source word for word. It says A.13 states only the weaker eigenvalue bound, and that the exact identities are a reconstruction with no novelty claimed. Whether this accurately describes MZ24 is a question about the cited paper, which was not available to me, so I have not verified it.
- **Disclaimers are intact:** the Status line, §1's "no complexity-class separation", the §2 statements that novelty and priority are not certified, the §11 statement that reviews were AI-only, and the Appendix's "not Lean verification".
- **C-1: date inconsistency.** The title page is dated **12 September 2026**, but §2 and refs [7]/[8] cite OpenAI preprints dated **23 September 2026**. Either the date or the "based on version 0.1.0" wording needs correcting.
- **C-2:** see T-7. One mathematical statement (the Lemma 1 conclusion) exists only in the renderer, not in the canonical source.
- **Outside this review:**
  - Mathematical correctness of any lemma or of the composition.
  - Formal (Lean) certification.
  - Novelty or priority.
  - Clearance to submit or publish.
  - The open Full105 items: Full105 has only conditional, scoped three-lens acceptance; runtime/source and the exact product/G-Φ/adjoint manuscript identities remain open. Nothing here changes that.

## 4. Verdicts

| Area | Verdict |
|---|---|
| **Visual** | **Conditional pass.** All 31 pages are readable; no glyph, clipping, overlap or reference failures. Cosmetic issues: V-1, V-2, B-1 |
| **Transcription** | **Not accepted.** T-1 to T-8 need fixing, mainly the lost pinpoint citation (T-3), the dangling contract references (T-4) and the renderer-only content with no recorded origin (T-7). B-2 and B-3 need bibliography fixes |
| **Claims boundary** | **Conditional pass.** Disclaimers are preserved; C-1 (date) and C-2 (renderer-written Lemma 1 conclusion) need resolution |
| **Overall** | **NO GO.** This review covers visual and transcription content only; it does not cover mathematical proof, formal certification, novelty or publication clearance |
