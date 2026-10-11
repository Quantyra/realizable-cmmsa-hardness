# Independent all-page visual and source-to-PDF review (v5): *Realizable Nearlinear-Gap Hardness for Small Monotone Formulas*, 32 pages

I inspected all 32 pages and skipped none. I checked each page image together with its text layer. Small sub- and superscripts were checked against the text layer and `body.tex` at the resolution provided, which is not a font-level check. As instructed, I used no tools, so I did not recompute any SHA-256 hashes. I traced content through `submission-manuscript.md` → `render_manuscript.py` → `body.tex` → `correspondence.json` → preamble and `references.bib` → PDF.

**Verdicts**

| Lens | Verdict |
|---|---|
| Visual | **Accept with minor findings.** No clipping, overlaps, broken glyphs or bad page transitions. |
| Transcription and notation repair | **Accept with minor findings.** The repairs keep every statement the same. |
| Claims boundary (draft disclosure) | **Accept as a draft disclosure, with wording findings.** All open gates are stated. This is not a judgment on the proof. |
| Mathematical proof, formal certification, novelty, publication | Not assessed and not cleared. |
| **Overall** | **No GO.** |

## 1. Per-page coverage

| Pg | Contents | Result |
|---|---|---|
| 1 | Title, URL, date, abstract ("we present a proposed…"), keywords, new Status paragraph, §1, YES/NO items | Clean |
| 2 | Theorem 1, (1.1), learning model, Corollary 1, (1.2), scope disclaimer | Clean |
| 3 | §2 with [3], [2], [5], [6], [5, 6, 1], [8, 7]; §3 notation | Clean. Citation lists are unsorted (cosmetic). |
| 4 | Contracts 1–4 | "MZ Theorem" ends the page and "5.5." starts p5 (V3) |
| 5 | End of contract 4; contracts 5–7, (3.1), navigation sentence, Lemma 1 statement | Clean; `label` is now upright |
| 6 | (4.1)–(4.3), proof □, §5 with **"β=loglog J/J"**, §6 intro | loglog restored |
| 7 | Lemma 2 and proof, Lemma 3 statement | Clean |
| 8 | Lemma 3 proof, π(c,k), GL-action display, homogeneous experiment | Clean; wide displays stay inside the margin |
| 9 | End of Lemma 3 □, Lemma 4, adjoint/composition displays, λ_i cases, **MZ24 A.13 attribution** | Clean; faithful to source |
| 10 | End of Lemma 4 □, Lemma 5, ambient conditions, Markov step, ‖L‖ bound | Clean |
| 11 | K_inv/D_inv, selection step, f-averaging, cutoff | Clean |
| 12 | λ display, Lemma 5 □, Lemma 6, F_n display | Clean |
| 13 | End of Lemma 6 □, "Bin(J,β)" (now roman), (6.1), (6.2) | "3J-2D" uses a hyphen (V1) |
| 14 | (6.3)–(6.7); **"Q ⊆ L"** | F1 fixed. "2^c-1" and "3J-2D" use hyphens (V1). |
| 15 | (6.8), (6.9), **"Q ⊆ L ⊆ W"**, §6.1, **"Q ⊆ V"**, 2^{−6h²}−2^{−20h²}−2^{r+1−2J} | F1 fixed and the minus chain is now one math run. "2hm(ξ-1000ρ)" is still upright and hyphenated (V1). |
| 16 | End of §6.1, §6.2, **"Q ∩ H_U={0}"**, (6.10), (6.11), **"W ∩ V"** ×2, start of §6.3 | F1 fixed. "(2^b-1)/(2^n-1)" and "3J-2T" use hyphens (V1). |
| 17 | End of §6.3, (6.12), §7, rows 1–5 of the table | Clean |
| 18 | Repeated table header, rows 6–7, K/B block, (7.1), (7.2) | longtable continues correctly across the page |
| 19 | (7.3), end of §7, §8, (8.1)–(8.3) | Clean |
| 20 | Hoeffding step, §9, (9.1)–(9.3) | Clean |
| 21 | End of §9, §10, (10.1)–(10.3), closing □, start of §11 | Clean |
| 22 | End of §11 (AI-review disclosure), Appendix A, footnote 1, Theorem 2, §A.1 | Footnote URLs break cleanly |
| 23 | (A1)–(A3), §A.2 | Clean |
| 24 | (W6), EKL counterexample, §A.3, (DR6) | Clean |
| 25 | Φ, (A4), (A5) | Clean; the wide hat renders correctly |
| 26 | §A.4, (T1), (A6), (T2) | "Holder" (V2) |
| 27 | Proof of (T2), (A7), (A8), (A9) | (A8) fits the margin |
| 28 | (A10)–(A12), §A.5, (A13)–(A15) | Clean |
| 29 | (A16)–(A18) | Clean |
| 30 | §A.6, (A19)–(A21), §A.7, (A22), (A23) | "Holder" (V2) |
| 31 | End of §A.7, proof of Theorem 2 □, closing remark, References [1], [2] | See §3 |
| 32 | References [3]–[8] | See §3 |

**Structural checks**

- There are 30 numbered displays, matching `display_count: 30`.
- Tags (A1)–(A23), (W6), (DR6), (T1) and (T2) are all present.
- Lemmas 1–6, Theorems 1–2 and Corollary 1 are present, and every □ is there.
- No `??` references appear.
- Every citation number maps to the right key: [1] BKM, [2] Hir22, [3] HN, [4] KMS, [5] MZ, [6] MZ24, [7] OAI2to1, [8] OAIUG.

## 2. Notation repairs since the prior review

| Prior item | v5 status | Statement preserved? |
|---|---|---|
| **F1** subset/intersect printed as words (7 places) | **Fixed.** New `special` entries handle Q⊆L, L⊆W, Q⊆V, Q∩H_U={0} and W∩V. Longest-match ordering keeps the "Q⊆L⊆W" and "W(Q)∩V" phrases intact (p16–17). | Yes. The symbols are exactly the source relations. |
| **T2** loglog given a base it doesn't have | **Fixed.** `loglog(J)` → `\operatorname{loglog}J`, so the base stays unspecified as in the source. | Yes |
| **F2** hyphens used as minus signs | **Partly fixed.** Runs joined by `\)-\(` (p15 chain, C−2^{−10h²}) are now one math expression. **V1, still open:** cases where a digit sits between the hyphen and the next math run are not merged, e.g. `3J-2D` (pp13–14), `3J-2T` (p16), `(2^c-1)` (p14), `(2^b-1)/(2^n-1)` (p16), `2hm(ξ-1000ρ)` (p15, where "hm" is also upright). | Yes, just typographically uneven. |
| **F3** `label` and `Bin` in math italic | **Fixed.** Both are roman. The second "label(y)" is upright text rather than `\operatorname`, which looks equivalent. | Yes |
| **F4** Hölder/Holder | **Still open (V2).** The inherited literal appendix block still says "Holder" (pp26, 30). I agree with the root that no math changed. | Yes |

Apart from the above, I did not find dropped sentences, reordered arguments, or changed constants or exponents. I re-spot-checked these against the source:

- 1000ρ / 1000ρ²
- 2^{500i²p}
- the 2^{−6h²}/2^{−8h²}/2^{−9h²}/2^{−10h²} ledger
- the bound in (A10)
- (A21)
- (8.1)
- (8.3)
- the 9/16 bound in (9.2)
- (10.3)

Two remaining notes:
- **V3:** the "Theorem / 5.5." page split (p4→5) could be avoided with `Theorem~5.5`.
- **Minor:** `T_1[L+H_{U_0}] | L` (p16) renders the restriction bar as `\mid`, which predates v5.

## 3. Bibliography underfull notices (six)

I checked pp31–32 directly.

- Nothing overflows the margin and nothing is clipped or overlapping.
- All eight entries are complete.
- Stretched spacing is visible in [5] (first line) and [7] (first two lines), with lighter stretch in [2] and the long-URL lines of [6] and [8].
- I can't match each of the six notices to an exact line, and I don't claim a mapping. All of them fit the pattern of long unbroken URLs.

There are two cosmetic issues:
- **[7]:** the URL breaks right after `https:`.
- **[8]:** the URL breaks at a hyphen that is part of the URL (`The-Unique-Games-` / `Theorem-…`), so a reader can't tell whether the hyphen belongs there.

Also, `howpublished` gives "23 June, 2026" ordering in [3] and [6], and "28 October, 2025" in [5].

**Assessment:** acceptable. Optional fixes are `xurl` or a ragged-right bibliography.

## 4. Claims boundary (separate from visual and transcription)

**Draft status is now explicit and keeps every gate.** The Status paragraph (p1) and §11 (pp21–22) together state:

- the work is a proposed informal argument under continuing review;
- Full105 has conditional scoped acceptance only;
- source/selection/sampler and encoded-runtime obligations are open;
- native exact product, G/Φ, adjoint and packaged cross-level identities are incomplete;
- formal certification, novelty clearance and publication acceptance are not claimed;
- the paper is not submitted;
- the reviews are AI reviews, not human peer review or Lean verification.

The abstract now says "we present a proposed…". §11 says that the incomplete native identities "do not by itself refute the separate informal arguments". That matches the instruction that a missing Lean translation is not a refutation. The prior "not cleared" finding is resolved for disclosure purposes.

**Wording findings (low, not blocking):**

- **C1.** Readers can't tell what "native" means. It could be read as saying the informal identities in Lemma 4 are incomplete. Suggest "Lean-native formal translations of the exact product, G/Φ, adjoint…". "Full105" is an internal label with no definition; suggest naming it or describing it. The status also omits "three-lens", which is less specific but not misleading.
- **C2.** Some phrasing still asserts completion: "We now prove the parameter extension and the remaining composition in full" (p5), and "This completes the proofs of Theorem 1 and Corollary 1" (p21). The Status paragraph qualifies both, but they read awkwardly beside the open source/selection/sampler obligations. Suggest "complete the proposed argument". Theorem 1 and Corollary 1 are stated without hedges, which is normal for a draft that carries a status disclaimer.
- **C3.** §11 writes "G/Phi" in ASCII while the Status paragraph writes "G/Φ". This is cosmetic.
- **MZ24 A.13 (p9).** The attribution is faithful to the source and renders correctly. Its accuracy depends on MZ24 rev. 1, which this review did not check. The same holds for the bridges to MZ Lemma 4.5 and MZ24 A.17–A.18, and for the claim that the Ellis–Kindler–Lifshitz weight-4d bound fails.
- Novelty and priority remain hedged correctly.

## 5. Remaining items

1. V1: merge the remaining hyphen/minus cases (`3J-2D`, `3J-2T`, `2^c-1`, `2^b-1`, `2^n-1`, `ξ-1000ρ`) and set "hm" as math.
2. V2: spell Hölder consistently in the appendix literal block.
3. V3: use `Theorem~5.5`.
4. C1–C3: identify "native" as Lean translation, gloss Full105, soften "in full" and "completes the proofs", and use Φ in §11.
5. Optional: `xurl` or ragged-right for the bibliography.
6. Still open, and outside what a visual review can clear: the full source/selection/sampler, runtime and native-translation gates; mathematical proof acceptance; formal certification; novelty clearance; publication.

**Overall: NO GO.** The visual and content checks pass for release as an explicitly labelled draft. This verdict makes no claim about whether the proof is correct, formally certified, novel or ready for publication.
