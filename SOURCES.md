# Sources and theorem dependencies

The complete new argument is in [MANUSCRIPT.md](MANUSCRIPT.md). Established
inputs are cited rather than reproved. The versions below determine the
contracts; similarly titled revisions are not silently substituted.

| Key | Primary source and inspected version | Use |
|---|---|---|
| HN | Shuichi Hirahara and Mikito Nanashima, *A Sharp Characterization of Pessiland*, ECCC TR26-052, revision 1, June 23, 2026. [Revision PDF](https://eccc.weizmann.ac.il/report/2026/052/revision/1/download/), [revision record](https://eccc.weizmann.ac.il/report/2026/052/). | Definitions 1.2, 1.7, 3.11, 4.1; Theorem 3.5; Lemma 4.6 and Section 4.3; Lemma 5.1; target Theorems 1.3/1.8 and Section 7. |
| MZ | Dor Minzer and Kai Zhe Zheng, *Near Optimal Hardness of Approximating k-CSP*, arXiv:2510.23991v1, October 28, 2025. [Versioned HTML](https://arxiv.org/html/2510.23991v1), [versioned PDF](https://arxiv.org/pdf/2510.23991v1). | Theorem 3.1, Claim 3.2, Section 3.3, Lemmas 3.3--3.4, Theorem 4.2, Definition 5.4, Section 5.4.1. The altered repetition analysis is proved in this manuscript. |
| MZ24 | Dor Minzer and Kai Zhe Zheng, *Near Optimal Alphabet-Soundness Tradeoff PCPs*, ECCC TR24-027, revision 1, May 13, 2026. [Revision PDF](https://eccc.weizmann.ac.il/report/2024/027/revision/1/download/), [arXiv v4](https://arxiv.org/html/2404.07441v4). | Theorem 5.26 with delta=rho/m, including its Lemmas 5.24--5.25 conditions; Claim 3.2 supports the general outer-game ancestry. Only the advice/codimension range 10m/rho is needed. |
| KMS | Subhash Khot, Dor Minzer and Muli Safra, *On Independent Sets, 2-to-2 Games, and Grassmann Graphs*, Theory of Computing 21(10), 2025. [Article](https://theoryofcomputing.org/articles/v021a010/), [PDF](https://theoryofcomputing.org/articles/v021a010/v021a010.pdf). | Definition 4.5 and Lemmas 4.6--4.7, proved unconditionally in Section 8; used for arbitrary fixed repetition and joint conditioning. |
| Hir22 | Shuichi Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*, FOCS 2022. [Conference PDF](https://ieee-focs.org/FOCS-2022-Papers/pdfs/FOCS2022-4Bu7jGV9xIcveUWYj3oWoi/551900a968/551900a968.pdf). | Earlier realizable learning hardness (Theorem I.1) and the underlying reduction credited by HN; HN p.5 explicitly records the realizable CMMSA L^alpha bound. |
| BKM | Amey Bhangale, Subhash Khot and Dor Minzer, *On Approximability of Satisfiable k-CSPs: I*, TheoretiCS 5 (2026), article 9. [Journal record](https://doi.org/10.46298/theoretics.26.9), [arXiv v4 PDF](https://arxiv.org/pdf/2408.15377v4). | Related-work comparison on perfect-completeness dictatorship tests; not an imported hardness premise. |

The HN revision explicitly retracts its earlier small-superconstant
parameter claim. Our reductions fix L before input length. The HN PDF
inspected by the independent source reviews had SHA256
`cce323afdddf5c5bb61ab9a8079513080813fce6216c1a44a2891c5c67c387c4`.

The MZ [STOC 2026 record](https://doi.org/10.1145/3798129.3800728) exists,
but its publisher full text was not accessible during the assessment.
The author-linked arXiv full version was v1. Our numerical observation
concerns that version alone and does not allege an error in an uninspected
camera-ready proof or refute the source's main theorem.

MZ v1 Theorem 5.5 prints a larger advice range involving J. This artifact
uses the independently checked narrower MZ24 Theorem 5.26 specialization,
whose constants depend on m,rho, not J. Covering lemmas are proved KMS
results; their use does not import UGC or its historical combinatorial
hypothesis. The manuscript states the new posterior and threshold arguments
separately from these imported results.

The literature assessment on September 12, 2026 checked the corrected HN
question, its cited earlier realizable result, current MZ version histories,
and satisfiable-CSP comparisons. It identified no exact subsumer. This is
a targeted source assessment, not exhaustive priority certification, review
of every unpublished manuscript, or contact with the cited authors.
