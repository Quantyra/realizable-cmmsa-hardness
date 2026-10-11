# Proof and API map: selected physical density

## Profiles

`ActualNumericPhysicalDensity.physicalScoreExponent M h` is the exact natural repetition exponent `Q=2*M*(h - 4000*(h / bOf M))`. The selector output `M` is the star count throughout; the `Instance N rows` occurrence-row count remains independent.

`selected_explicit_parameters` translates the exact selector output for the captured `numericSourceFloor` through `selected_numeric_height` at the enlarged base. It returns `M >= 256`, `numericHnum M <= hBlock L M`, and `bOf M | hBlock L M`; the Hnum bound includes the rank floor and the explicit scalar/cutoff floor. The source-height input is never moved to an earlier selector or base.

`selected_ordered_carriers_nonempty` takes the same selector output, the sampler parameter `A`, padding `Tpad >= 4`, and `0 < rows`. It uses the derived geometric bounds and calls `taggedGoodU_nonempty_of_padding` to construct the eligible U carrier, `taggedCenterOver_nonempty` to construct every center fiber, and `taggedLeafOver_nonempty` to construct every leaf fiber. The main wrapper's explicit `[Nonempty TaggedGoodU]` and center/leaf proof arguments are exactly the values supplied by this constructor theorem; they expose the source-row and padding construction instead of assuming an inhabited source instance silently.

`selected_physical_density` fixes one instance, selector output, center table `C`, and arbitrary raw table. Its physical-score premise is the original strict premise `(1/2)^Q < taggedPhysicalMass` for the same ordered law and fixed tables. It derives `alpha=(1/2)^(Q+1) <= taggedPhysicalMass`, all numeric guards, and the slack `2^-J + 16*S <= alpha` with `S=successMargin (badExponent M h)`. It then calls `ordered_physical_forces_MZ_threshold_U` with `k=M` and `t=leafT M h`. The output keeps the entire eligible-U uniform mass sum and one canonical table `T'`; it does not reduce the mass conclusion to a single eligible U.

## Arithmetic path

Let `b=bOf M=4000*M^2`, `q=h/b`, and `J=blocks A h`. The exact explicit selector floor yields `numericHnum M <= h`; `numericRank_le_Hnum` gives `10*M*b <= h`. Divisibility gives `b*q=h`, hence `10*M <= q`. Since `b>=4000`, `4000*q<=h`, so the natural subtraction in `Q=2*M*(h-4000q)` is exact. The same quotient gives `leafK=2q` and the exact split `leafT+leafK=2h`.

The sampler interface `A*h^2 < blocks A h` and `A>=1` gives `h^2<J`. The rank floor makes `h >= 2*M+2`; consequently `2*M*h+2 <= h^2`, `2h<=J`, and `M^2<=h^2<J<=2^J`. Also `Q<=2*M*h`, so `Q+2<=J`. With `leafK=2q`, `2J-2h>=J` and `q>=1` imply the geometry guard `2J <= (2h-leafT)*(2J-2h)`.

Write `E=badExponent M h=2*M*(h-1000q)`. Since `E-Q=6000*M*q>=6`, `(1/2)^E <= (1/2)^(Q+6)`. Therefore `16*S <= (1/2)^(Q+2)`. The guard `Q+2<=J` also gives `(1/2)^J <= (1/2)^(Q+2)`. Adding yields the `16*S` slack at `alpha=(1/2)^(Q+1)`. Separately, the original strict score `(1/2)^Q < physicalMass` implies `alpha<=physicalMass`, as required by the ordered physical theorem.

## Exact dependencies

The physical-density conclusion is `ActualTaggedFixedUDensityForce.ordered_physical_forces_MZ_threshold_U`. Fiber constructors are `ActualTaggedOrderedSampleNonempty.taggedCenterOver_nonempty` and `.taggedLeafOver_nonempty`; eligible-row construction is `ActualTaggedOrderedQuestionSourceBridge.taggedGoodU_nonempty_of_padding`. Selected Hnum and divisibility come from captured `ActualNumericExplicitHeight.numericSourceFloor` and `ActualNumericSourceHeight.selected_numeric_height`; `numericHnum`, `numericRankThreshold`, and the explicit floor are from `ActualNumericExplicitHeight`. `successMargin` is from `ActualStarAcceptedGoodMass`; `leafT`, `leafK`, and `badExponent` are from `ActualStarFixedRhoDimensionGuard`; sampler growth is `SamplerParameters.numerator_lt_blocks`.

## Claims boundary

This is an uncompiled source offer. The wrapper's strict high physical-score premise remains conditional on the same fixed source instance and tables. It does not prove that a SAT construction supplies that score, identify source rows with selector M, or discharge robustness, NO soundness, reduction-size, or runtime obligations. No conditioned or reweighted law is substituted for the unconditioned ordered physical law.