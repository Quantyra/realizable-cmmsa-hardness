# Realizable Nearlinear-Gap Hardness for Small Monotone Formulas

For every sufficiently large **fixed** leaf bound L, this note proves
randomized polynomial-time many-one NP-hardness of realizable weighted
CMMSA with gap L^(1-o(1)) and a vanishing NO satisfaction threshold.
Hirahara--Nanashima's transfer gives the corresponding fixed-advice
realizable learning statement.

Read the complete [manuscript](MANUSCRIPT.md), including definitions,
imported theorem contracts, the full new proof, and the exact learning
corollary. [Sources](SOURCES.md) identify the versions and prior results;
[review disclosures](REVIEW.md) explain the AI derivation and checking roles.

The result establishes the epsilon=0 strengthening asked in Section 7 of
Hirahara--Nanashima's June 23, 2026 revision. Earlier realizable hardness
is due to Hirahara; the improvement here is the nearlinear exponent.
The proof combines established PCP, compilation and learning results with
an explicit parameter, posterior, threshold-ladder and completeness-repair
argument. Novelty and priority are not certified.

Each L is fixed independently of input length, and the reduction's
polynomial exponent may depend on L. The result does not settle the
separate superconstant-parameter question, attain a linear approximation
factor, construct one-way functions, or resolve P versus NP.

Version 0.1.0 | Quantyra Research | 12 September 2026.
Informal AI mathematical review; no human peer review or machine-checked
proof is claimed. Citation metadata is in [CITATION.cff](CITATION.cff).
Original artifact content is licensed under [Apache 2.0](LICENSE);
external works retain their own copyrights and licenses.

Version correction: 0.1.0 is the current research-preprint version. The
initial GitHub release was labeled 1.0.0; that historical tag and release
are preserved. This correction changes version/archive metadata only;
the theorem statements, proofs, source attributions and review findings
are unchanged. The Zenodo archive metadata identifies this work as a preprint.

Archived publication:

- Version 0.1.0 DOI: [10.5281/zenodo.22728702](https://doi.org/10.5281/zenodo.22728702).
- Concept DOI (all versions): [10.5281/zenodo.22728701](https://doi.org/10.5281/zenodo.22728701).

Use the version DOI to cite this exact archived preprint.

Companion Lean sources for **certified components** (GO / GO-WITH-NOTES, not the full manuscript theorem) live in [`lean/`](lean/README.md). They do not replace the informal manuscript proof, do not inhabit unconditional Theorem 1 or Corollary 2, and do not change this archived preprint.
