# Independent final review: conditional CMMSA core (`ActualSelectedComplementAnalyticMargin`)

**Overall: GO-WITH-NOTES on all three lenses for this conditional core.** No HIGH findings. Five MEDIUM and seven LOW findings are listed below. The verdicts come from reading source, not from the build result.

## Role, model and how I worked
- **Role:** one independent final reviewer, working read-only. I used only Read, Grep and Glob. I edited nothing, ran no compiler, changed nothing in Git, started no cloud resources and delegated to no agents.
- **Model:** Claude Opus 5.5 (`claude-opus-5-5[1m]`), as stated in my system context. I can't attest to anything beyond that.
- **Checking the pinned file:**
  - I could not compute SHA-256, because none of my read-only tools hashes files. So I have **not verified** `26A2011F…` or `CF8E6397…`.
  - Instead I compared the main file with the snapshot `margin-observed-26A2011F.lean.snapshot`. Both have 3,659 lines and the same count of `theorem`/`def`/`sorry`/`axiom` matches (83). The snapshot's lines 3586–3659 match the main file's exactly.
  - I did not open the run235043 receipts or audits.
- **Basis for the verdicts:** my own reading of the source, plus comparison with `paper/body.tex` (Lemma `lem:inverse-explicit` at lines 360–519 and Theorem `thm:binary-hc` at 908–920).

## Files reviewed
- **Read in full:**
  - `ActualSelectedComplementAnalyticMargin.lean` (lines 1–3659) and its `…Checks.lean`
  - `ActualSelectedComplementAnalyticMoment.lean` lines 1–1240, which includes both contracts and `selected_actual_analytic_rhs`
  - `ActualSelectedComplementAnalyticNumerics.lean` lines 1–440
  - `ActualOriginalFailureRowGenericFixedMomentCaller.lean`
- **Statements or definitions only:**
  - `BinaryMatrixFourier` (`PseudorandomExact`, `AffineRestriction`, `lpNorm`, `rankProjection`)
  - `ActualMaximalPairLadder` (`Zoom`, `agreement`, `codim`)
  - `ActualCmmsaAdmissibilitySelector`, `ActualCmmsaParameterReconciliation`
  - `ActualSelectedSpectralParameters.selected_spectral_parameters`
  - `ActualStarFixedRhoDimensionGuard` definitions
  - `ordinary_star_selects_weighted_functional`
  - `sideConditionalDensity_le_uniformComplement_average_StarDensity`
  - `matchingStarMass_actual_coordinate`, `starLaw_pushforward_actual`
  - `source_failed_zoom_to_selected_coordinate`
  - `actual_leaf_failed_zoom_gives_nominal_pseudorandom`
  - `matchingStarMass_cast_le_twice_actualAppendRankImageMoment`
  - `doubled_high_error_budget_le_additive_half`
- **Scan:** none of the files that define these declarations contain `sorry`, `admit` or `axiom`. Across the whole `lean/PvNP` tree, `native_decide` appears only in `ActualCnfQueryStarChecks.lean`; I didn't trace the full import closure, but that is a separate Checks module.

## What checks out (proof structure)
1. **Original score and universal failed family**
   - `hscore` is the actual `sideConditionalDensity ≥ successMargin(badExponent m h)` (Margin:3038).
   - `hfailSource` covers every complement A and every (q, Q, P) with `q + codim P.W = sourceRankExponent m` and a nonempty zoom (Margin:3046–3057).
   - The quantifier order is correct. In `yields_bad_zoom`, assuming no bad zoom gives a rational e with floor < e < 2·floor, failure holds for all A at that e, and the contradiction follows (Margin:3624–3656).
2. **Same A and same f all the way through**
   - A and `fCoord` come from one witness (Margin:3189–3195).
   - `fSource = fCoord ∘ actualCoordinateEquiv`, and `coordinateFunctional fSource = fCoord` is proved (Margin:3196–3202).
   - `hfailSource A`, the fixed-moment caller, the selector bundle and the strict comparison all use this same A, `Cc`, `Tc` and `fCoord` (Margin:3322, 3544–3552).
3. **Signals and β**
   - The selector gives `S/4·(M/B)·β + S/4·(M/F) ≤ X ≤ β`. This matches the manuscript: X ≥ (ε/4)·2^{−ms₀}·β + (ε/4)·2^{−(t₀+ms₀)} (body.tex:476).
   - The β floor is derived, not assumed.
   - `β ≤ 1` is proved from the star law (Margin:769).
4. **Mass equality and the source-to-coordinate score:** the mass equality is exact, in ℚ, via pushforward along an equivalence. The coordinate score is derived from an exact event-law equality (Margin:63–214). Complement selection averages in the valid direction (Bound:137).
5. **Parameters versus the manuscript**
   - r = 40000m³ = 10m/ρ with ρ = 1/(4000m²).
   - S = 2^{−2(1−1000ρ)mh}.
   - The agreement floor is e = 2^{−2(1−1000ρ²)h} (body.tex:365–366 matches Numerics:28).
   - The threshold is η = 2^{−(20/3)mh} = 2^{−(2/3)rρh}.
   - The Hölder bound is T ≥ 16000m(m+3) = 4(m+3)/(mρ).
   - The PR parameter is 2e, rounded via `2e < 4·floor`.
   - The selection guard is `m·s + E + 2 ≤ 2J − c`, matching body.tex:458.
6. **Strict comparison**
   - 2·low ≤ first summand, using the proved exponent bound ≤ −1 (Margin:900–1220).
   - 2·(threshold + tail) ≤ additive/2.
   - Hence 2·RHS ≤ first + additive/2 < X, which contradicts X ≤ 2·RHS (Margin:2681–2947).
7. **Exact P and independent rows**
   - `RowGeneric.fixedMomentP`, `FixedMomentCaller.fixedMomentP` and `sourceMomentP` all unfold to 2^{m·2^{16000m(m+3)}}.
   - Rows are independent of m: the margin uses `Instance N rows`.
8. **Natural-number subtraction:** every truncating subtraction is guarded:
   - `1000·(h/b) ≤ h`
   - `c + m·s ≤ n`
   - `2h − c = s`
   - `m + 1 ≤ h − 1`
   - `c + s − 1` with c + s = 2h > 0
9. **No hidden final bounds in the hypotheses:** the three exports take only I, U, C, T, `cutoff`, `hsel`, `hA`, `hscore`, e, `hfailSource`, `he`, `he'`, HC46 and Spectral47. None is a margin, β, PR or moment bound.
10. **The conclusion isn't trivial:**
    - The rank budget forces `codim P.W ≤ r ≪ 2J`, so a zoom never shrinks to a single leaf.
    - For a random table, agreement is about 2^{−2h}, far below the floor.

## Findings
| Sev | Location | Finding |
|---|---|---|
| MEDIUM | Moment:35–40 vs body.tex:908–920 | **The core holds vacuously if `HC46ExactContract` is false.** The contract drops the manuscript's 0 ≤ δ ≤ 1 hypothesis. By my own pen-and-paper argument it is equivalent to Thm binary-hc: δ<0 is vacuous because a zero-direction restriction of budget r always exists, and δ>1 follows from the δ=1 case. That theorem remains an open obligation, and nothing in the repo witnesses that the contract is consistent. |
| MEDIUM | Moment:45–58 | **Same vacuity exposure for `Spectral47ExactContract`.** It looks provable: for basis-invariant F the ratio is a Gaussian-binomial quotient ≤ 2^{−is}, consistent with body.tex:355. I have not verified this formally. |
| MEDIUM | Margin:3032–3036, Selector:24–41 | **`hsel` uses the constant base `fun _ => sourceMarginHeightFloor m`, tied to the output m.** Only the admissibility half of `selector_spec` is used. The output of a natural, j-indexed selector need not satisfy this hypothesis. This is an applicability gap (already listed as open); soundness is unaffected. |
| MEDIUM (complexity) | Margin:501–510 vs body.tex:422–424 | **T and P are much larger than the manuscript's.** Lean uses T = 2^{16000m(m+3)} and P = 2^{mT}; the manuscript asks for any dyadic T ≥ 16000m(m+3) and the *least* dyadic P ≥ mT. P is exact and dyadic, but this makes the height floor tower-sized in m instead of polynomial. The admissible m therefore grows far more slowly in L. |
| MEDIUM (complexity) | SamplerParameters:12 | **The ambient dimension far exceeds L.** J = 2^{2^{A·h²}} with h ≈ log L. The core makes no claim about encoding size. |
| LOW | Margin:3609–3622 | **The bad zoom is weaker than "the selected complement has a bad zoom".** It is stated for *some* complement A, on `transportedLeafTable`, not on the original tagged T. Mapping it back is downstream work. |
| LOW | MarginChecks | No non-vacuity example for `hsel` / `hscore` together. |
| LOW | Margin:2681 ff. | **Valid alternative routes.** The low term uses Hölder at P/m (exponent β^{1−m/P}) rather than the manuscript's mT route. The high term is absorbed by the additive signal rather than half of the first summand. Both are proved. |
| LOW | Selector:25; Numerics:49 | **Narrower scope than the manuscript.** It is fixed to ρ = 1/(4000m²) with m ≥ 256 and bOf m dividing h; the manuscript allows m ≥ 2 and 0 < ρ ≤ 1/4000. |
| LOW | Margin:3096, 3158 | Two duplicate `fixedMomentP` definitions are mixed in the first export. They are definitionally equal. |
| LOW | Margin:2056, 3017, 3355 | Debug settings left in: `pp.all true` and `diagnostics true`. |
| LOW | Moment:917 | The older `k < 8m` moment variant is unused. The core uses `…_large_dyadic`. |

## Verdicts
- **Proof-adversarial: GO-WITH-NOTES.**
  - The logic, quantifiers, same-witness discipline, exponent arithmetic and guards are sound as stated.
  - The conclusion matches body.tex:371–374: agreement > e on a nonempty zoom with dim Q + codim W = r.
  - The main caveat is the vacuity exposure from the two contracts.
- **Complexity: GO-WITH-NOTES.**
  - The core asserts nothing about complexity, uniformity, promise problems or reductions.
  - The non-minimal T and P, and J ≫ L, must be handled by any downstream parameter or runtime argument.
- **Non-claims: GO-WITH-NOTES.**
  - The docstrings are accurate. The Moment header (lines 11–14) explicitly says the contracts are not proved locally, and the exports state no final margin, β, PR or moment input.
  - The core is not a proof of any of the following, which remain open explicit obligations:
    - HC46 or Spectral47 inhabitants
    - manuscript, classical, supporting, robust8S or numericNO steps
    - source-star or encoded-runtime steps
    - selector applicability
    - global closure
  - `ActualBinaryMatrixHC46.lean` was excluded and not reviewed.

## Limits and what I didn't review
- I checked only the statements, not the proof bodies, of the imported lemmas listed above. That includes:
  - the matrix-lift factor 2
  - rank-loss ≤ 2
  - coordinate zoom transport
  - cross-level orthogonality and Parseval
  - the high-error budget
  - the dimension guard
  - side-law equals complement average
- I did not check whether those proof terms are accepted by the Lean kernel; that is outside a read-only review.
- I did not check whether the manuscript's Thm binary-hc proof (appendix after line 920) is correct.