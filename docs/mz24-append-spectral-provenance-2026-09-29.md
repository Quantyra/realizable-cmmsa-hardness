# MZ24 append spectral provenance

S3126/S3132/E004 primary-source audit; no Lean edits, compiler or git actions.

MZ24 is Minzer–Zheng, *Near Optimal Alphabet-Soundness Tradeoff PCPs*, STOC 2024, pp. 15–23. The matching appendix is pinned [arXiv:2404.07441v1](https://arxiv.org/html/2404.07441v1#A1), 11 April 2024, not the subsequently revised unversioned paper.

Fresh inspection resolves the previous bibliographic/appendix hold:

- A.10 preserves basis invariance under rank projection.
- A.11 gives the append/restriction inner-product identity only when its leaf-side function is basis invariant; the restriction operator is expressly not an unrestricted adjoint.
- A.12 identifies their composition with the additive operator under the same invariance premise.
- A.13 gives rank-zero eigenvalue one; positive-rank absolute bound `3*q^(i−n)+q^(−i(s−1))`.

These statements introduce no explicit additional ambient cutoff. Their operators require valid integral widths c+s=2h and full-rank rectangular restriction factors. The append definition's expectation subscript shows fewer vectors than its argument; its explanatory sentence specifies s appended columns, matching the later binary paper. Preserve this source inconsistency in provenance; use the unambiguous binary operator already aligned locally.

Application boundary: retain basis invariance, even total width, valid integer split and nonempty full-rank sampling carriers. No universally quantified arbitrary-function adjoint contract is justified. Actual selected ambient arithmetic, analytic estimates and conditional-core application remain separate obligations.
