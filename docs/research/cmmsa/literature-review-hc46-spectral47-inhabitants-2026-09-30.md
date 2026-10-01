# HC4.6 / spectral 4.7 inhabitants: T3 route review (2026-09-30)

## 1. Trigger, route, and current evidence

**Trigger: T3**, the named residual matching a classical hard step; route-decision review is required before another material analytic-proof increment. This is a canon-first review of the manuscript's already stated finite inequalities, not a proposal for a new force lane. Planning context: S3137 (formal analytic-chain/full theorem), S3132 (outer game and star-PCP/source-force gate), and S3126 (paper/proof consolidation). The boundary map routes this manuscript-specific Lean work to this satellite, `realizable-cmmsa-hardness`; it does not route new work to `formal-pvnp`.

The selected-complement analytic-moment source and its Checks are kernel-green at the reported 26A snapshot. That proves the source-shaped conditional composition and its checked interfaces only. The source still takes `HC46ExactContract` and `Spectral47ExactContract` as hypotheses; no inhabitant of either universal contract is exported. The three required Codex lenses have completed **GO-WITH-NOTES** for this bounded conditional increment. This is not a review of the full theorem or its missing analytic-contract inhabitants. Green conditional composition is not the analytic engine or a route-final result.

Planning's literature-review trigger protocol calls T3 for a named classical residual and requires a 3-8 row gap table, next-story routing, non-claims and a stop-loss. The satellite contains no `AGENTS.md` or `docs/protocol.md`; the supplied planning boundary and the paper's own source record govern this review.

## 2. Canonical target and exact contract shape

The manuscript appendix `paper/submission-manuscript.md`, section “Finite binary matrix hypercontractivity,” states and proves its **Binary Boolean matrix inequality**. For Boolean `F : Mat_{n,D}(F_2) -> {0,1}`, `0 <= delta <= 1`, and every consistent restriction of nominal budget `r` having conditional density at most `delta`, it claims for every `0 <= i <= r` and dyadic integer `p >= 4`:

```text
||F^{=i}||_p <= 2^(500 i^2 p) delta^(1 - 2/p).
```

The nominal budget counts columns of the right restriction plus rows of the left restriction. Dependent and zero equations are included; lower-budget restrictions are handled by padding. The appendix says it reconstructs the finite argument and its auxiliary estimates rather than importing a hypercontractive theorem. It attributes the method to Ellis--Kindler--Lifshitz and the globalness/dyadic applications to Evra--Kindler--Lifshitz. The source itself disclaims Lean verification and novelty.

The current Lean interface is `ActualSelectedComplementAnalyticMoment.HC46ExactContract`:

```lean
forall {n d h r i p : Nat} {eta : Real}, d = 2*h ->
  (b : BinaryMatrix n d -> Bool) ->
  PseudorandomExact r eta b -> i <= r -> 4 <= p ->
  (exists q : Nat, p = 2^q) ->
  lpNorm p (rankProjection i (indicator b)) <=
    (2 : Real)^(500*i^2*p) * eta^((p-2)/p)
```

`PseudorandomExact` is the exact nominal-budget predicate: all affine restrictions in its domain with budget exactly `r`, when the restriction fibre is nonempty, have conditional density at most `eta`. This is not a convenient weaker predicate or an arbitrary selected functional. The failed-zoom route derives it for the same selected leaf Boolean with `eta = 2*e`; the analytic theorem must still be proved for every such Boolean and all displayed parameters.

`Spectral47ExactContract sourceHeightCutoff` universally quantifies `n,c,s,h,i,rho`, an arbitrary real matrix function `F`, and full basis invariance under every matrix and every pair of two-sided inverse matrices. It retains `c+s=2*h`, `i<=c+s`, `0<rho`, the exact real split equations `c=2(1-rho)h`, `s=2rho h`, and the source height cutoff. This cutoff is an extra caller guard in the formal contract, not a hypothesis required by MZ Lemma 4.7 itself. The conclusion is the normalized append-average squared-energy estimate

```text
uniformMean_M (appendAverage (rankProjection i F) M)^2 <=
 (2^(-i*(s-1)) + 3*2^(i-n)) * uniformMean_W (rankProjection i F W)^2.
```

This contract is stronger than the selected Boolean instance: it is for all real `F` satisfying the stated invariance. Do not replace it with a selected-function-only premise. The paper's finite-character spectral lemma is the canonical target, with exact eigenvalue weights and the displayed weaker error bound; the manuscript states the matrix and spectral bridges are proved there.

The independent spectral source trail is Moshkovitz--Zhu, *Near Optimal Hardness of Approximating k-CSP*, Lemma 4.7 and its proof, which invokes MZ24 Appendix A.10--A.13 ([paper arXiv:2510.23991v1](https://arxiv.org/abs/2510.23991v1), [PDF](https://arxiv.org/pdf/2510.23991v1), Lemma 4.7 at pp. 15--16). The cited MZ24 is Minzer--Zheng, *Near Optimal Alphabet-Soundness Tradeoff PCPs* ([arXiv:2404.07441v1](https://arxiv.org/abs/2404.07441v1), [PDF](https://arxiv.org/pdf/2404.07441v1), Appendix A pp. 60--63): A.10 shows rank-level projections preserve basis invariance; A.11 gives the extension/restriction adjoint identity under basis invariance; A.12 identifies the composed operator with a Cayley averaging operator; A.13 diagonalizes on characters and bounds the eigenvalue by the ambient-error plus decay terms. For HC, MZ Theorem 4.6 attributes the finite inequality to EKL24 and points to MZ Theorem A.7 for its exact formulation; the manuscript's own appendix reconstructs the finite proof and records EKL22 as method source ([EKL22](https://arxiv.org/abs/2209.04243v1), [EKL24](https://arxiv.org/abs/2404.00641v2)). These sources support the mathematical targets and provenance, not local Lean certification.

## 3. Literature-to-formal gap table

| Step | Canonical/source status | Satellite formal status | Required next evidence |
|---|---|---|---|
| Finite Boolean HC inequality, constant 500 | Explicit theorem and self-contained finite appendix proof in the manuscript; MZ Theorem 4.6 points to EKL24 | Only universal `HC46ExactContract` interface; no Lean inhabitant | Kernel proof of the exact contract, including normalization, endpoints and all exact-budget restrictions |
| Nominal restriction budget and padding | Manuscript defines the budget and permits dependent/zero equations; appendix gives padding argument | `PseudorandomExact` captures exact-budget, nonempty affine fibres | Prove the finite restriction/globalness bridge in Lean without changing the budget or fibre semantics |
| Dyadic exponent and Boolean projection | Manuscript states dyadic `p>=4`, rank-`i` projection and `delta^(1-2/p)` | Contract carries those quantifiers; selected caller obtains its concrete `p` | Formalize the full dyadic Boolean inequality, not just a selected `F` instance or a helper lemma |
| Finite spectral/append-energy estimate | Manuscript finite-character lemma supplies exact weights and the weaker spectral bound | `Spectral47ExactContract` is universal over `F`, basis changes, and inverse pairs; selected application/energy tail helpers exist | Prove the universal finite-character/append-average statement with the exact `c,s,h,rho` and height guards |
| Conditional moment-to-source witness composition | Manuscript inverse argument and 26A Lean conditional composition are present | Green Checks verify conditional composition from HC46 + Spectral47; both contracts remain inputs | Inhabit both contracts, then rerun focused checks and complete the separate source/PCP/review gates |

## 4. Next story routing

1. **S3137 / HC46**: the next bounded mathematical story is the exact HC46 universal inhabitant, beginning with the appendix's finite binary-matrix hypercontractive chain and nominal-budget padding. Candidate new module: `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean`, importing only the existing finite-matrix/Fourier foundations needed for the source proof. Export a theorem inhabiting `HC46ExactContract` with all universal parameters, exact nominal-budget predicate, dyadic premise and constant 500 unchanged. Do not edit the green moment module to hide this proof.
2. **S3137 / Spectral47 (separate module and theorem)**: prove the exact universal append-energy contract from the manuscript finite-character lemma. Candidate module: `lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47.lean`; export an inhabitant of `Spectral47ExactContract sourceHeightCutoff`, retaining arbitrary real `F`, all inverse pairs, exact split and source cutoff. Do not treat the selected high-tail/Parseval helper as that theorem.
3. **S3132, then S3126/S3128 as applicable**: after the two analytic inhabitants, resume the actual fixed-center/source-force and reduction obligations; only then refresh the manuscript crosswalk/fresh-checkout consolidation. The representative-law identity alone supplies no upper bound (S3132's existing boundary).

For each candidate, add a focused Checks file that profiles the exported contract inhabitant and its actual dependencies, then ask Sol to run the pinned serialized Lean diagnostic and preserve the source/object receipt. Only after both inhabitants build should the existing conditional composition be re-run against them; the formal three-lens review remains a separate required gate. These are routing recommendations, not story completion or authorization to claim the outer game closed.

## 5. Non-claims

This review does not claim the HC46 or Spectral47 contracts are Lean-proved, that the 26A conditional composition establishes them, that S3132's source-force/fixed-center issue is solved, or that the full realizable-hardness theorem, PCP/reduction, encoded runtime, or publication result is complete. The manuscript's ordinary mathematical proof is evidence for the target, not a kernel receipt. The GO-WITH-NOTES Codex reviews cover the bounded conditional increment only; they do not certify the full theorem or either missing contract inhabitant.

## 6. Stop-loss: no packaging without an inhabitant

Stop after a bounded attempt at the source-derived HC46 finite proof and the source-derived Spectral47 proof. Do not open another packaging/helper/carrier lane, change the contract to fit an existing helper, add an assumption supplying either final bound, or call the conditional moment theorem a closure. If a real mismatch with the manuscript appears, record the exact statement/line and pause for a route decision or source correction. A green build without both contract inhabitants is not progress toward the central analytic result by itself.

## 7. Decision

**Continue narrowly, pinned to the manuscript's existing finite engine.** The mathematical route is source-backed: the paper already contains the finite Boolean HC proof and finite-character spectral proof, and primary literature independently locates the HC theorem. The missing work is their faithful Lean formalization, not a new theorem-shaped wrapper. Pin the exact contracts above; the first mathematical frontier is to formalize the appendix's nominal-budget restriction/padding plus finite HC chain until it yields `HC46ExactContract` with the unchanged dyadic exponent and constant 500. In parallel, track Spectral47 as its own universal theorem. Pivot only if that formalization exposes a concrete false statement or source-to-contract mismatch; do not pivot merely because the conditional composition is green.
