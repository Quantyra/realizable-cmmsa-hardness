# Proof-adversarial review

Reviewer: fresh top-level Codex agent `/root/proof_adversarial_review_235043`, GPT-6 Astra, xhigh.

**Verdict: GO-WITH-NOTES for the pinned conditional core.** No HIGH or MEDIUM proof defect found. No source changes are required by this review.

Reviewed Main SHA256 `26A2011F190746E0B80788C42C7C0F0C1120A31D6D0FD8A3E09569999A1ABCCC` and full Checks SHA256 `CF8E63970FD89732C1395A38E6D93C42E965E29B028489FABA3C9FA430A12101`.

All paths below are relative to `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness`.

- **Original score and selected witness preserved.** `lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean:3038` takes the original side-conditioned score. Lines 3046?3057 quantify failure over every source complement, advice space and decoded pair. The proof selects `A,fCoord` at line 3189, defines `fSource` by the same coordinate equivalence at line 3196, and proves its coordinate image equals `fCoord` at line 3199. The exported mass equality starts at line 3111. I found no replacement complement, functional or table.
- **Score transport uses the valid direction.** `ActualSelectedComplementAnalyticMargin.lean:350` bounds the original score by the uniform complement average, selects a complement, then uses exact acceptance-event transport. The underlying inequality is `ActualTaggedComplementStarDensityBound.lean:137`; it does not reverse the one-sided matching-good-mass comparison.
- **Both signal terms survive.** `ActualSelectedComplementAnalyticMargin.lean:2655` retains the weighted term plus the unconditional additive term. The latter yields positive beta. Lines 2757?2774 pay for the outer factor two in the low contribution; lines 2884?2946 bound the remaining contribution by half the positive additive signal and obtain the strict comparison.
- **Exact parameters and moment retained.** `ActualSelectedComplementAnalyticNumerics.lean:28` defines the agreement floor using `rho?`; `ActualSelectedComplementAnalyticMargin.lean:433` uses `rho` in the original success scale. The fixed moment definitions at `ActualOriginalFailureRowGenericFixedMomentCaller.lean:227` give `K = 2^(16000*m*(m+3))`, `P = 2^(m*K)`. Its source-mass bound at line 352 uses that exact `P`, `eta = 2*e`, and the supplied threshold. Main supplies `manuscriptMomentThreshold` at line 3160. The row count and analytic moment index remain independent.
- **Final inverse has no external no-bad-zoom premise.** `ActualSelectedComplementAnalyticMargin.lean:3586` exports an actual source complement and nonempty decoded zoom with the exact rank budget and agreement strictly above the original floor. `hNoBadZoom` occurs only as the local contradiction assumption at line 3624. The rational threshold between the floor and twice the floor is constructed internally.

Counterexample attempts did not expose a defect:

- Empty complements are excluded by the explicit complement construction at Main line 328. Selector-derived dimension proofs at lines 2950 and 2987 supply nonempty Grassmann centers and leaves.
- Zero beta cannot satisfy the positive additive signal; positivity is established at Main line 2827.
- Oversized exact restriction budgets do not make HC pseudorandomness vacuous: `BinaryMatrixFourier.lean:323` allows unrestricted nominal row/column counts and zero equations, permitting padded whole-space restrictions.
- Negative `eta` cannot satisfy that padded nonempty restriction premise. The `eta=0`, rank-zero and zero-dimension cases did not yield an inconsistent HC instance.
- Spectral degeneracies did not expose an impossible contract: with positive height, the split equations restrict `rho`; with zero height, `c=s=i=0` and the displayed coefficient is at least one.
- The coordinate failure bridge transports arbitrary decoded functionals, zoom cardinalities and agreement, rather than only restrictions of a selected global functional: `ActualCoordinateZoomFailureTransport.lean:85`, `:158`, and `ActualOriginalFailureAnalyticCaller.lean:21`.

**LOW scope note:** `ActualSelectedComplementAnalyticMoment.lean:35` and `:45` remain universal analytic hypotheses. This review found no concrete inconsistency in them; it does not construct their inhabitants or establish joint inhabitation of all application premises. `hsel`, `hA`, the eligible `U`, the original score, and the cutoff remain explicit boundaries. Full manuscript certification, robust8S/numericNO/source-star integration, encoded/runtime reduction, and top-level switching/PvNP claims remain outside this approval.

Evidence independently checked:

- All 24 overlay source pins match current files.
- Run235043 input archive matches SHA256 `4a054b86a252cc21ed49633d45db3944af13959f8ca8014796095b84866b90c2`.
- All 194 local Lean files in Main?s import closure match archived source semantically: 123 byte-identical, 71 differing only by CRLF/LF, no substantive differences or missing dependencies.
- Raw receipts report five prebuild exits `0`, native exit `0`, and successful full Checks build with 3391 jobs.
- All 27 Main axiom profiles, including the three requested full exports, contain only `propext`, `Classical.choice`, and `Quot.sound`. No placeholder or new-axiom declaration appeared in the 24 pinned inputs.

This was a read-only source and receipt review. I did not run Lean, mutate Git/files, or operate cloud resources.

Custody: transcribed from the actual Codex reviewer response; original also retained in its agent thread. Path spelling normalized to forward slashes.
