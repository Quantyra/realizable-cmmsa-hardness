# Actual numeric-NO scalar envelope and contradiction

This is an uncompiled candidate source translation. The exact source-shaped material bound is retained, including its outer factor 2 and both middle/high terms. This source proves the finite low-HC envelope and a conditional scalar contradiction. It does not claim selector/sampler inhabitance, the same-instance signal, or a completed source theorem.

## Proof map

- `selected_low_HC46_envelope` bounds the actual finite sum `selectedLowHC46NormBound`. For every `i` in its source index set, `i <= r`, so the actual coefficient `2^(500*i^2*k)` is at most the endpoint coefficient. Since `(k-2)/k >= 0`, `eta <= 2*e0` gives the termwise power bound. The finite index set is a subset of `range (r+1)`; summing the nonnegative common endpoint bound yields the exact `(r+1)` envelope. Inputs include `k >= 4` and nonnegative `eta,e0`; there is no unjustified `r <= d` premise. No sum is replaced by a guessed constant.
- `actualWeightedHighEnergy_le` is imported from the captured v2 `ActualNumericNo`. It bounds the exact two-term high-rank coefficient sum using Boolean total rank energy, the ambient inequality `d+r*bdim+3 <= n`, and `bdim >= 1`.
- `conservative_material_scalar_contradiction` keeps `materialScalarRhs` as `2*(low + middle + B/a^2)`. It uses `a=2^(-(2/3)r*rho*h)`, derives the low envelope from the finite sum, bounds the unchanged actual high energy, and absorbs both high and middle terms into half the first same-instance signal term. It uses the exact beta lower bound and epsilon lower bound, derives the beta inverse-power bound, and converts the final product into `2^(log2(16*K)+2/T-lambda*h)`. The strict cutoff is exactly `(log2(16*K)+2/T)/lambda < h`.

## Same-instance source integration

`selected_actual_rhs_eq_materialScalarRhs` proves the exact RHS identity; `selected_actual_source_material_scalar` transports an upper bound through that identity. For a source caller, obtain `hSource` as the first conjunct of `ActualSelectedComplementManuscriptDyadicMoment.selected_actual_material_moment_bound_at_dyadic_exponent`, instantiated on the same `I,copies,U,A,C,T,f,base,sourceHeightCutoff,hsel,hA,r,e,hfail,hHC,hSpectral,a,k`. Apply the transport lemma with its output tables `Cc,Tc,fc`, `eta=2*(e:Real)`, `X` equal to its matching-star mass, `d=c+s`, and `n=2*J`. Set scalar `beta` to the exact Grassmann center-mass ratio; the source theorem's second conjunct identifies the matching-center mass with this ratio. Then the result supplies the scalar theorem's `hMaterial` directly, with the source's unchanged outer factor 2 and actual high-energy sum.

The same source instance must separately provide `hSignal`, `hXleBeta`, and the beta/epsilon links from the selected-star lower-bound argument. They are deliberately left explicit here: this candidate does not prove them or turn the external source/table data into an inhabited selector/sampler witness. The rational agreement maximum and actual `B` tail are exact source-level interfaces, but an end-to-end same-instance instantiation still needs an integration proof.

## Exact constants and cutoff

Write `S=2^(-2*(1-1000*rho)*m*h)`, `D=2^m+2^(r+1)`, and `K=2^(2*m)*(r+1)^m*2^(500*m*r^2*k)`. The low term is bounded by `2*K*beta^(1-1/T)*e0^(m-2/T)`: the leading 2 is the material consumer's outer factor and the second `2^m` comes from `(2*e0)^(...)`; neither is dropped. The middle and high terms are bounded together by `D*2^(-(20/3)*m*h)`. The absorption premise is

`log2(32*D) <= (((8/3)*m-2)+(3996*m+2)*rho)*h`.

The beta inverse-power estimate contributes `2^(2/T)*2^(2*(m+1)*h/T)`. Combining with `e0`, `epsilon >= S`, and `s=2*rho*h` gives the exact exponent `log2(16*K)+2/T-lambda*h-4000*rho^2*h/T`, where `lambda=2000*m*(rho-rho^2)-2*m*rho-2*(m+3)/T`. The proof bounds it above by `log2(16*K)+2/T-lambda*h`, establishes `lambda>0` from the displayed rho/T assumptions, and uses the strict cutoff to make the final bound less than one, contradicting the lower bound one.

## Evidence boundary

No Lean/Lake invocation, compiler, GCP, or Git operation was performed. `ActualNumericNoScalarChecks.lean` requests axioms for all four public declarations; these are requests, not results. The parent compiler owns the only compile/capture path. This candidate is not a kernel theorem, acceptance result, or proof of the still-open same-instance source and signal premises.
