# Numeric source-height candidate

This root-authored, uncompiled candidate translates the existing planning argument in `full90-actual-rhs-numeric-no-obligations-2026-10-08.md`, lines76–92. The separate author's source-height turn ended with provider request `c24e3749-384c-4c23-bb06-44db154a019a`; no files were observed at the assigned v1 path. That observation is not a raw provider transcript. This v2 source has not been parsed or checked by Lean.

Set `b=bOf(m)=4000*m^2`, `r=10*m*b`, and `basePlus j=max(base j)(10*j*bOf(j))`. The selector premise uses this enlarged base in the actual analytic floor. Applying the pinned `selected_spectral_parameters` to that same premise supplies `m>=256`, `b|h`, `basePlus(m)<=h`, the original base and analytic cutoff, and the exact selected real dimension identities. No old selector witness is reused.

Writing `q=h/b`, divisibility gives `b*q=h`. Since `b>0` and `10*m*b<=h`, cancellation gives `q>=10*m`, hence `s=leafK=2*q>=20*m` and `s-1>=1`. The exact identity `r*s=20*m*h` bounds `r*(s-1)` above. Moreover `b>=4000`, so `h>=40000*m` and `h>=20*m+5`; multiplying the latter by `h` proves `2*h+20*m*h+3<=2*h^2`. The existing sampler theorem with `A>=1` gives `h^2<blocks A h`. Together with `c+s=2*h`, this proves the exact tail guard `d+r*(s-1)+3<=n` for `d=c+s` and `n=2*blocks A h`.

The real-parameter export uses the source's exact `rho=1/b`, deriving `0<rho<=1/4000` and `r*rho=10*m` while retaining the selected `c=2*(1-rho)*h` and `s=2*rho*h`. Thus the scalar and finite-tail consumers can use the same selected parameters rather than an arbitrary numeric tuple.

Still open: existence of a selector output at this enlarged base, a computable common cutoff satisfying every scalar constraint, construction of the source/table/sampler instance, the lower signal, and integration with the captured numeric maximum and scalar candidates. This candidate establishes no inhabited witness, hardness result, runtime theorem, or certification. All four Checks are requests for future GCP evidence.
