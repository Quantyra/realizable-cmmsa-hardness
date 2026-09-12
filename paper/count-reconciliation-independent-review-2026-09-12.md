# Independent count reconciliation source review

2026-09-12. Reviewer `paper_count_review`, independent of correction author `guarantee_proof_review`. S3128/S3126. Candidate `0bd5dc988a4172359dc0e60b7b5a8b6e41bd1be3`; reviewed all six changed paths against its parent, the submission-source/archive diff, build/renderer relationship, and the frozen formal-pvnp count source.

**Verdict: GO-WITH-NOTES for this bounded source/content correction.** No blocking mathematical or transcription issue found in the changed count argument. This is not kernel acceptance, full-theorem certification, manuscript-wide mathematical approval, or current-PDF visual approval.

## Mathematical checks

For natural N_0 and positive epsilon with natural P >= 1/epsilon, P is positive and T = 32(N_0+11)P^2 >= 352 > 1. The exact analytic threshold equals 32(N_0 ln 2 + ln 12)/epsilon^2. Using ln 2 <= 1, ln 12 <= 11, and (1/epsilon)^2 <= P^2 gives threshold <= T. Minimality of e = clog_2 T gives T <= 2^e and 2^(e-1) < T; hence M = 2^e < 2T. These assertions include N_0 = 0. The inadmissible P = 0 case is not used.

The constructor exactly matches formal-pvnp `ComputableSampleCount.target`, `exponent`, and `count` at candidate `287b4e02997e94eb44572e228d8223f11ba045f4`. Current source diff against that candidate is empty. `learningThreshold_le_target`, `count_upper_of_inverse`, and `learning_budget` state the corresponding bounds; no independent Lean execution was performed by this reviewer.

The Hoeffding/union expression is 2^(N_0+1) exp(-2M(epsilon/8)^2), bounded by 1/6 under the log-12 threshold. Sampling-distribution error epsilon/8 plus empirical deviation epsilon/8 gives epsilon/4. Sampling success is therefore at least 5/6 and also at least the retained weaker 2/3 claim. Combining sampling failure <= 1/6 with transfer failure <= 1/6 on successful intermediate instances gives total failure <= 1/3 by conditioning/union bound; independence is unnecessary. The transfer premise itself remains an upstream obligation.

The manuscript chooses epsilon = Gamma/(16 sigma), Gamma = 2(3/4)^q, with positive sigma and all these parameters chosen from fixed L. Thus epsilon is positive rational and P = ceil(1/epsilon) is a computable natural constant relative to the outer input for fixed L. The numeric bound M < 64(N_0+11)P^2 is appropriate. It does not establish the support-materialization, bit-complexity, or full machine-runtime obligations. No uniform growing-L complexity result follows.

## Artifact and transcription checks

- Root `MANUSCRIPT.md` SHA256 remains `ff00997c8c243e88982c41b0b0e24faaaafe36cec6f1903824599dc242538686`. The entire source prefix before the count paragraph, including theorem/corollary statements, is identical. The remaining submission/archive differences are precisely the count replacement and two later success-accounting references.
- Submission source SHA256 is `491f54667880a85efe47fc5fd15cd371d6a945b21647a88f1acf6f748a99590b`. All 128 crosswalk span hashes, full normalized source hash, and 804-line count were independently recomputed and matched.
- Renderer AST parses. Its source points to `paper/submission-manuscript.md`, its count display matches that source, and its added inline expressions preserve the intended inequalities. The changed generated-body paragraphs match the source correction. `build.py` calls this renderer before LaTeX. The crosswalk hashes establish source correspondence, not visual or mathematical equivalence by themselves; this review separately inspected the changed display/prose.
- Generated body SHA256: `4f67ef020f7cb3b03d0d4d9499e24ca2598ab857e41c63b8cfaa5320a4a2240a`.
- Renderer SHA256: `c26eed3a932da626a7e9d40004351160fc0b0c05608e5bdfbf0ace7e12542d5e`.
- Correspondence JSON SHA256: `55c50568a98dc8d5e3c2165015452c900cc0508d8f1bb27b7cb80fdac392a26a`.
- PDF remains SHA256 `7282701f19d0427819f51f2afc1ac438ee5dcc02a64adb62b21cb61687ee37b9`; PDF/QA and original archive have no candidate diff. README and author receipt explicitly identify PDF/QA as stale. No assertion that the existing PDF reflects this correction was found.

## Remaining boundaries

Independent count kernel audit remains separately required. Full Lean formalization, specialized PCP/geometry/learning dependencies, encoded reduction runtime, final manuscript-wide reconciliation, and regenerated PDF visual QA remain open. This review approves proceeding to the reserved-capacity rebuild and its review, not publication or submission. No Lean/PDF build, network access, source mutation, push, release, or publication was performed. No destination AGENTS.md was present at root; the supplied planning/destination scope was followed. Only this independent review receipt was created.
