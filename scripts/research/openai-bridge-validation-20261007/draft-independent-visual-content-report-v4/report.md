# Independent all-page visual and source-to-PDF review: *Realizable Nearlinear-Gap Hardness for Small Monotone Formulas* (31 pp.)

The review is complete. I inspected all 31 pages from the attached page images and their text layer, and skipped none. As instructed, I used no tools, so I did not recompute any SHA-256 values. I compared content only: `submission-manuscript.md` → `render_manuscript.py` → `body.tex` → `correspondence.json` → preamble/`references.bib` → PDF.

I could see the page images, but only at the resolution provided. Where a subscript or superscript was too small to read in the image, I confirmed it against the text layer and `body.tex`. This is ordinary visual QA, not a check at the level of individual font glyphs.

**Verdicts:**

| Lens | Verdict |
|---|---|
| Visual | **Accept with minor findings.** No clipping, overlaps or broken glyphs. |
| Transcription | **Accept with findings.** No mathematical content was lost; there are stylistic leaks and one change of notation. |
| Claims boundary | **Not cleared.** The PDF claims a complete proof, and its disclosures do not reflect the open review items. |
| Overall | **No GO.** |

## 1. Per-page visual coverage

| Pg | Contents inspected | Visual result |
|---|---|---|
| 1 | Title, author URL, date, abstract, keywords, Status, §1 start, YES/NO items | Clean |
| 2 | Theorem 1, eq. (1.1), learning model, Corollary 1, eq. (1.2), §2 start, citations [3],[2] | Clean. Eq. (1.2) is aligned correctly. |
| 3 | §2 continued, [5],[6],[5, 6, 1],[8, 7], §3 notation, Gaussian binomial, start of Contract 1 | Clean. `[5, 6, 1]` is not sorted (cosmetic). |
| 4 | Contracts 1–5 | Clean |
| 5 | Contracts 5–7, (3.1), navigation sentence, Lemma 1 statement | "label" is set in math italic (F3) |
| 6 | (4.1)–(4.3), proof □, §5, §6 intro | `log2 log2 J` (T2) |
| 7 | Lemma 2 and proof, Lemma 3 statement and start of proof | Clean |
| 8 | Lemma 3: π(c,k), the GL-action display, homogeneous experiment; Lemma 4 operator display | Clean. The long conditional-expectation display fits the margin. |
| 9 | Lemma 4 statement end, adjoint/composition displays, λ_i cases, **MZ24 A.13 attribution** | Clean; the attribution is a faithful copy of the source (see §4) |
| 10 | Lemma 4 end, Lemma 5 statement, ambient conditions, Markov step, the ‖L‖ bound | Clean |
| 11 | K_inv/D_inv, selection step, cutoff, λ display, □ | Clean |
| 12 | Lemma 6 statement, F_n display, preservation and termination steps | Clean |
| 13 | Lemma 6 end □, (6.1)–(6.4) | "Bin" is set in math italic (F3) |
| 14 | (6.5)–(6.8) | **"Q subset L", "L subset W"** (F1) |
| 15 | (6.9), §6.1, §6.2 start | **"Q subset V", "Q intersect H_U"** (F1); "2hm" upright; chain of hyphens used as minus signs (F2) |
| 16 | (6.10), (6.11), §6.3, (6.12) | **"Q subset V", two occurrences of "W intersect V"** (F1) |
| 17 | §6.3 end, §7, 7-row table, start of the K/B block | The table fits on one page; the cell wrap "zoom-/outs" is fine |
| 18 | K/B display, (7.1)–(7.3), §8 start | Clean |
| 19 | (8.1)–(8.3), sampler, Hoeffding step | Clean |
| 20 | §9 (9.1)–(9.3), §10 (10.1) | Clean |
| 21 | (10.2), (10.3), closing □, §11, Appendix A, footnote 1 | Footnote URLs break cleanly |
| 22 | Theorem 2, §A.1, (A1), (A2) | Clean |
| 23 | (A3), §A.2 (W6), §A.3 (DR6) | Clean |
| 24 | Φ, (A4), (A5) | Clean; the wide hat in (A5) renders correctly |
| 25 | (T1), (A6), (T2) | "Holder" has no umlaut (F4) |
| 26 | Proof of (T2) in both directions, (A7), (A8), (A9) | Clean; (A8) fits the margin |
| 27 | (A10)–(A14) | Clean |
| 28 | (A15)–(A17) | Clean |
| 29 | (A18)–(A21) | Clean |
| 30 | §A.7, (A22), (A23), proof of Theorem 2, □ | "Holder" again (F4) |
| 31 | Closing remark, References [1]–[8] | Stretched lines and URL breaks (F5) |

**Structural checks:**
- **Displays:** there are 30 numbered displays, matching `display_count: 30`: (1.1)–(1.2), (3.1), (4.1)–(4.3), (6.1)–(6.12), (7.1)–(7.3), (8.1)–(8.3), (9.1)–(9.3), (10.1)–(10.3).
- **Appendix tags:** (A1)–(A23), (W6), (DR6), (T1) and (T2) all render.
- **Environments:** Lemmas 1–6, Theorems 1–2 and Corollary 1 are present, and every □ appears.
- **References:** I found no unresolved `??` references or citations.

## 2. Findings (severity)

**F1 – Pseudo-notation printed as words (minor, transcription and visual).** Seven places print ASCII notation as prose:
- p. 14: "Q subset L", "L subset W"
- p. 15: "Q subset V", "Q intersect H_U={0}"
- p. 16: "Q subset V", "W intersect V" (twice)

The source contains these words. The renderer's `special` map only converts the exact strings `Q subset L subset W`, `W(Q) intersect V` and `L intersect H_U={0}`, so other occurrences pass through as text. Elsewhere the PDF prints ⊆ and ∩, which makes these spots inconsistent. The meaning is still recoverable.

**F2 – Hyphens used as minus signs (minor, visual).** Inline expressions such as `1-ϵ`, `3J-2D`, `C-2^{-10h²}` and `2^{-6h²}-2^{-20h²}-2^{r+1-2J}` (p. 15) set the minus as a text hyphen between math fragments. The p. 15 chain is the hardest to read. "2hm" (p. 15) is set upright.

**F3 – Words set in math italic (cosmetic).** `label(x_i)` (p. 5) and `Bin(J, β)` (p. 13) are italicized like products of variables. A related, faithfully copied notation issue: the italic e in (6.3) is Euler's number, but it looks the same as the density e from Lemma 5.

**F4 – Inconsistent spelling (cosmetic).** Lemma 5 has "Hölder", but the appendix has "Holder" (pp. 25, 30). The source uses both spellings.

**F5 – Bibliography underfull notices (cosmetic; acceptable).** I checked page 31 directly:
- Nothing extends past the margin, nothing is clipped, and there are no overlaps.
- Inter-word spacing is visibly stretched in [2], [5], [7] and [8].
- The [7] URL breaks right after `https:`; the [8] URL breaks at an existing hyphen (`The-Unique-Games-` / `Theorem-…`), so a reader can't tell whether the hyphen belongs to the URL.
- All eight entries are present and correct for the `.bib` file: [1] BKM, [2] Hir22, [3] HN, [4] KMS, [5] MZ, [6] MZ24, [7] OAI2to1, [8] OAIUG. Every in-text number matches its key.

Without the log line numbers I can't match each of the 8 notices to a specific line. All of them are consistent with stretch from long URLs. An optional fix is `xurl` or a ragged-right bibliography. Separately, entries [3], [5] and [6] print as "23 June, 2026", an awkward order produced by `howpublished`.

**T2 – Notation changed during rendering (low).** Source §5 has `beta=loglog(J)/J`. The renderer's special map turns this into **β=log₂log₂J/J** (p. 6), adding a base that the source does not state. It makes no asymptotic difference, but it attributes a specific form to MZ's displayed choice. Either put `loglog` back or check it against arXiv v1.

**T3 – Disclosed editorial changes (accepted, noted):**
- Keywords and the Status paragraph were added.
- The navigation sentence "Lemma 1 gives… Sections 6–10…" was added.
- Source **Corollary 2 is PDF Corollary 1**; this is recorded in `correspondence.json`, but anyone citing the source by number will be off by one.
- `REVIEW.md` and `SOURCES.md` links became the prose "companion review disclosures" / "the bibliography", so a PDF reader can't find the review disclosures from the PDF.
- The closing sentence was expanded.

## 3. Transcription assessment

I compared every source paragraph and display against the PDF in order, including the 520-line literal LaTeX block for Lemmas 2–6 and the appendix, which passes through unchanged. Apart from T2 and F1, I found no dropped sentences, reordered arguments, altered constants or wrong exponents.

I spot-checked the following against the source:
- 1000ρ / 1000ρ², 500i²p, the 2^{−6h²} / 2^{−20h²} / 2^{−10h²} chain
- (A10) 100d²−63dt−4dk, (A21) 200d²p²
- σ = ⌊R^{1−1/m}/16⌋, T = 32(N₀+11)P², the 9/16 bound in (9.2), and σ_L = ⌊⌊σ/4⌋/2⌋

## 4. Claims boundary (separate from visual and transcription)

- **MZ24 A.13 (p. 9).** The sentence "MZ24 Lemma A.13 states the weaker eigenvalue bound, rather than the exact eigenvalue and energy identities below" is copied faithfully and renders correctly. Whether it is true depends on MZ24 rev. 1, which this review did not check. The same applies to the Lemma 3 bridge to MZ Lemma 4.5 and MZ24 A.17–A.18, and to the claim that the Ellis–Kindler–Lifshitz weight-4d bound fails (p. 23).
- **The PDF overstates the current status.** It says "We now prove … in full", "This completes the proofs", and that it "establishes the ϵ=0 strengthening". Lemma 4 states the exact identity ‖𝒯F_i‖² = λ_i‖F_i‖² and the G𝒯 = Φ / restricted-adjoint steps as proved. These are the exact product, G-Φ and adjoint native identities that remain open. The Status paragraph discloses only that the Lean formalization is incomplete and that the paper is unsubmitted. It does not mention Full105's conditional, scoped three-lens acceptance or the open runtime/source items. Section 8's "do not certify an encoded machine runtime" is the only partial hedge.
- **Novelty and priority:** these are hedged correctly ("does not certify novelty or priority"; "no novelty is claimed"). This review does not establish novelty or priority.
- **Out of scope:** mathematical correctness, formal certification and publication clearance. This review makes no claim about any of them.

## 5. Recommended pre-release fixes (non-blocking for visual acceptance)

1. Convert the seven `subset` / `intersect` occurrences in the source.
2. Put back `loglog`, or confirm `log₂log₂` against MZ arXiv v1.
3. Use proper minus signs in inline mixed expressions, and typeset `label`/`Bin` in roman.
4. Make the "Hölder" spelling consistent.
5. Optionally use `xurl` or a ragged-right bibliography.
6. Extend the Status paragraph to state that the result is conditional and to name the open identities and runtime items.
