# Actual explicit numeric height floor v2

Status: uncompiled source translation offer. It contains Lean proof bodies and fully qualified axiom-profile requests; no theorem is claimed compiled, kernel-checked, axiom-profiled, or accepted.

## Construction

For m >= 256, the source defines bOf m = 4000*m^2 and r = numericRankThreshold m = 10*m*bOf m. It sets T = 4*(m+3)*bOf m, x=m*T, q=Nat.clog 2 x, and k=2^q. `numericK_rounding` states x <= k < 2*x, 4*m <= k, and the explicit dyadic witness k=2^q. Only k is dyadic; T is an integer and need not be dyadic. These are the material-caller requirements hkDyadic and hkm pinned in Full110.

The exponents are N=4+2*m+m*(r+1)+500*m*r^2*k, Hfinal=2*bOf(m)*(N+2), and Hnum=max r (max (r+7) Hfinal). `numeric_floor_polynomial_bound` provides the conservative explicit bounds T<=32000*m^3, k<64000*m^4, N<=52000000000000000*m^11, and Hnum<=500000000000000000000*m^13.

## Scalar cutoffs

`numeric_scalar_cutoffs` applies at any h>=Hnum. It uses rho=1/bOf(m) and this T. It establishes T>=4, 4*(m+3)/(m*rho)<=T, k>=4, m*T<=k, e0<=1/2 for the exact scalar e0, the absorption cutoff logTwo(32*D)<=C*h, and the strict final cutoff (logTwo(16*K)+2/T)/scalarLambda<h. Here D and K are exactly the imported scalar definitions with r=numericRankThreshold(m). The K bound uses r+1<=2^(r+1), hence 16*K<=2^N and logTwo(16*K)<=N. The strict final comparison uses scalarLambda>=m*rho/2 and h>=2*bOf(m)*(N+2); no equality is substituted for the inequality.

## Same-selector composition

`numericBase base j=max(base j)(Hnum j)`. `numericRank_le_Hnum` and `numericSourceBase_eq` establish Hnum>=r and hence that the source candidate's inner max with r is redundant. `numericSourceFloor` therefore feeds exactly `numericBase base` into the unchanged analyticSourceHeightFloor, preserving the supplied spectral cutoff and the outer selector j+2 floor. `selected_explicit_numeric_parameters_eventually` applies the pinned `selector_unbounded` to this exact floor and converts only by the proved floor-function equality to the source-height v3 interface. For each eventual selected m and its same hBlock L m, it obtains Hnum<=h, the original base/cutoff/divisibility guards, the actual rho/c/s identities from `selected_numeric_real_parameters`, the dyadic/material and scalar cutoff statements, and the actual sampler tail budget. It uses no selector witness from a smaller base or another instance.

The theorem remains relative to the caller-supplied `base`, `cutoff`, sampler A, and M. It does not construct a source/table/sampler witness, selected-star lower signal, effective common satisfying spectral/source cutoff, polynomial-in-SAT-length selector threshold, complete encoded reduction/runtime, or the same-instance beta/epsilon links. In particular Hnum's polynomial bound is only in the numeric selector parameter m.

## Exact dependencies and evidence boundary

The parent source-height v3 capture is `numeric-source-height-offer-capture-v3/ActualNumericSourceHeight.lean`, SHA-256 `98661E33A9C272CB983368B60C12BF7AA7BE833076A5545CAB1CDF4917209BDF`; its capture index is `7CD8C1D6463A39ECDE018F278360847F6874C3F8A2A3CB57FFC2D687B025C96D`. The parent scalar v6 capture is `numeric-scalar-offer-capture-v6/ActualNumericNoScalar.lean`, SHA-256 `002998DCDBF10A2A145524078C6DA32545004D68C8A2AD45C2B34F6337B628FF`; its capture index is `3EB1E16820BE3B30BF51C39907ADFFF443A4E03D178D5B6B840F61F98BDACBC9`. Parent source-height v3 remains immutable and uncompiled. Material caller identity and assumptions are pinned by dependency archive `C1702903ECC5F939B9504371D63F0D4313E192446971EF0DD7627F6E770F3C61`, declaration `selected_actual_material_moment_bound_at_dyadic_exponent`.

This candidate has not been run through Lean/Lake/GCP. The Checks are axiom-profile requests only. No native verification, external review, proof certification, or acceptance is claimed.

## v2 static repair notes

The cutoff theorem conclusions are named `numericKRoundGuards` and `numericScalarCutoffGuards` propositions. This lets the eventual selector theorem state those propositions instead of placing theorem proof terms in proposition positions. The floor equality uses `max_eq_right` with `numericBase j <= numericHnum j`. The lower dyadic guard explicitly commutes `4*m` from the `m*4` consequence of `4 <= T`. The absorption proof chains both max inequalities from `r+7` through `max (r+7) Hfinal` to `Hnum`; the strict final comparison derives `1 <= m` before multiplying the nonnegative N term. The comparison `N <= Hfinal` also uses an explicit nonnegative-factor multiplication, avoiding reliance on nonlinear arithmetic to invent a product bound.

The intended construction, constants, and open-claim boundaries are unchanged. This is a source-only, uncompiled development offer. The named proposition interfaces and all tactic translations still require the root-owned native Lean diagnostics.

## Pinned API review

Read-only inspection used the Full111 package-source archive's exact `Mathlib/Data/Nat/Log.lean` (SHA-256 `7990e6e80987dde2e0c79fbedd77521d1dba8b4285e06d20feb0d8ca96f62bd9`). The signatures match the `Nat.clog_pos (hb) (hn)`, `Nat.pow_pred_clog_lt_self (hb) (hx)`, and `Nat.le_pow_clog (hb) x` applications in `numericK_rounding`; `Nat.succ_pred_eq_of_pos` supplies the predecessor-successor identity used to derive the strict upper rounding bound.

The same pinned archive's `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` is SHA-256 `5f4970fe329b14615ca6cfa3e0dcb0cf9d2017c98d2e3501237412aa2474e70b`. It gives `Real.rpow_le_rpow_of_exponent_le` with base premise `1 <= x`, `Real.rpow_neg` with nonnegative base, `Real.log_rpow` with positive base, and `Real.rpow_add` with positive base. The source uses these premises at base 2 or beta positivity, as appropriate. This is source/API inspection only and does not establish that the full tactic scripts elaborate.
