# MZ classical analytic contract conditions

S3126/S3132 source audit, 2026-09-29. This is a source-condition assessment, not an independent review of this note or an inhabited Lean contract. No Lean edits or compilation were performed. The planning T3 note permits classical subcontracts; actual moment/inverse/robust-8S conclusions remain internal obligations.

## Pinned primary statements

[Minzer–Zheng, Near Optimal Hardness of Approximating k-CSP, arXiv:2510.23991v1](https://arxiv.org/abs/2510.23991v1), submitted 28 October 2025; [versioned full text, §2.2 and §4.2](https://arxiv.org/html/2510.23991v1#S4), freshly inspected.

Use leaf width D=2ℓ, center width c=2(1−ρ)ℓ, append width s=2ρℓ; retain integral nonnegative dimensions. The operator averages F([M,B]) over all B∈F₂^(n×s). Measures are uniform. Definitions 2.2–2.4 use consistent affine equations MU=V, XM=Y, with nominal column-plus-row budget exactly r; no independence condition is stated.

Theorem 4.6: Boolean F, exact-budget (r,η) pseudorandomness, i≤r, dyadic p≥4 imply

`||F_i||_p ≤ 2^(500 i² p) η^((p−2)/p)`.

No basis-invariance or explicit η≤1 premise appears in this displayed statement.

Lemma 4.7: basis-invariant F, 0≤i≤D imply the SQUARED estimate

`||T F_i||₂² ≤ (2^(−i(s−1)) + 3·2^(i−n)) ||F_i||₂²`.

Equation (7) asserts orthogonality of distinct POST-operator levels; its proof separately invokes MZ24 A.10–A.13. It is not supplied by the per-level estimate.

Theorem 4.6 cites EKL24 and MZ24 A.7. [Evra–Kindler–Lifshitz v2](https://arxiv.org/abs/2404.00641v2) is distinct from [Ellis–Kindler–Lifshitz v1](https://arxiv.org/abs/2209.04243v1). Their inhabitants were not checked here.

## Local compatibility and open application obligations

| Local API | Alignment / remaining obligation |
| --- | --- |
| `BinaryMatrixFourier.rankProjection:252`, `lpNorm:319` | Real-valued normalized Fourier rank projection and natural-p norm. Boolean indicator is embedded in real functions; uniform normalization is explicit. |
| `AffineRestriction:323`, `PseudorandomExact:351` | Exact nominal budget and nonempty uniform fibre are already represented; preserve these quantifiers. `Pseudorandom:345` uses up-to budget and requires a padding proof before interchange. |
| `ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom:70` | Supplies the actual leaf lift at η=2e under unchanged failed-zoom assumptions. Any η≤1 side condition added by a downstream arithmetic argument needs a selected-e proof; it must not silently become a new classical premise. |
| `ActualFixedFunctionalAppendOperator.appendAverage:261` | Accepted unconditional all-matrix append law; `actualBinaryMatrixMoment_eq_actualAppendRankImageMoment:278` consumes that law with one shared center. |
| `ActualRankImageRightBasisInvariance.rankImageBoolean_mul_right_eq:78` | Accepted all-matrix invariance under explicitly paired inverses, including deficient matrices. Conversion to a GL-quantified contract binder remains an interface application if required. |
| Actual mass bound / analytic application | `hdV`, positive leaf width, and `hsmall` remain explicit. Selected numerical guard derivation, dyadic p choice when products of moment exponents occur, and post-operator cross-level orthogonality remain internal work. |

Restrict source contracts to even leaf width D=2h and c+s=D unless a separately checked general rectangular-width theorem is supplied. The displayed spectral statement contains no additional ambient lower bound; retain any conservative bound needed by the local proof as a local hypothesis. This audit supplies neither a final actual-moment upper-bound field nor an inverse/decoder/core field. A18/A21/A22 and classical contract inhabitants remain deferred outward under the recorded core-first phase policy.
