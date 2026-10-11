# Same-instance numeric composition: argument and API map

**Status: unstable source work.** The Lean source currently contains only the
private rational-power ratio lemma; the exported composition theorem and its
Checks have not yet been added. No Lean command has been run. This file does
not claim a proof or acceptance.

## Intended theorem

For one fixed actual occurrence `I`, copies, tagged good subspace `U`, globally
predrawn center and leaf tables `C,T`, sampler exponent `samplerA`, and a
concrete selector output `selector (numericSourceFloor base cutoff) L = m`,
assume the original unconditioned side density is at least

`Real.rpow 2 (-(2 * (1 - 1000 * actualSelectedRho m h) * m * h))`,

where `h = hBlock L m`. The conclusion chooses one complement `A` from this
same data and gives `q,Q,P`. Internally the weighted selector chooses one
functional `f`; that same `f` is retained throughout source-size and scalar
steps, although it is not part of the returned agreement predicate.
The output has
`q + codim P.W = numericRankThreshold m`, nonempty `Zoom Q P`, and strict real
agreement above
`Real.rpow 2 (-(2 * (1 - 1000 * rho^2) * h))` for the exact table
`fun X => selectedCoordinateLeafTable I copies U A T X`.

## Proof route and exact API boundaries

1. Rewrite the selector premise using `numericSourceBase_eq` and apply
   `selected_spectral_parameters (numericBase base) cutoff`. This supplies
   `m ≥ 256`, `m+2 ≤ h`, `bOf m ∣ h`, `leafT+leafK=2h`, the exact real split,
   and `actualSelectedRho=1/(bOf m)`.
2. Apply
   `ActualNumericExactThreshold.successMargin_badExponent_cast_eq_actualSelectedPower`
   to turn the real side-density premise into the rational
   `successMargin (badExponent m h) ≤ sideConditionalDensity` premise.
   `ActualGlobalDensityBridge.exists_complement_with_star_density_ge` then
   chooses one `A` with the transported ordinary star density. The bridge
   preserves `I`, `U`, `C`, and `T` and uses the unconditioned finite law.
3. `selected_numeric_height (numericBase base) cutoff` gives the numeric
   height floor. `fixed_numeric_tail_parameters` gives `1 ≤ leafK-1` and the
   ambient tail bound. `fixedRho_ambient_dimension_guard`, together with
   `sideComplement_finrank`, gives the weighted selector guard. Apply
   `ordinary_star_selects_weighted_functional` to the transported tables to
   choose `f` and the same-star `X, beta` signal.
4. Convert the selector's literal rational factors
   `M/B = 2^(n-(t+m*s))/2^(n-t)` and
   `M/F = 2^(n-(t+m*s))/2^n` using `rat_pow_ratio_cast`. The guard gives
   `t+m*s ≤ n`, hence the exponent differences are `m*s` and `t+m*s`.
   Cast the selector inequality to `Real` and rewrite with the exact threshold
   cast identity. Derive `0 ≤ beta ≤ 1` from `eventMass_nonneg`,
   `eventMass_mono`, and `eventMass_univ`; derive `hBetaLink` from the second
   signal summand and `X ≤ beta`.
5. Negate the desired exact-real conclusion for this same selected table.
   `actualAgreementMaximum_cast_le_of_failure` and
   `actualAgreementMaximum_gives_hfail` yield the exact rational all-zoom
   premise for the finite maximum, including every decoded pair and every
   admissible `q`.
6. Apply
   `selected_actual_material_moment_bound_at_dyadic_exponent` to the same
   `A,C,T,f`, using `original_HC46_exact` and
   `sourceSize_spectral47_inhabited cutoff`. Its two outputs are the actual
   material RHS and the same-`f` matching-center ratio identity.
   `selected_actual_source_material_scalar` rewrites the RHS to
   `materialScalarRhs`; the scalar theorem obtains the Boolean rank-energy
   `B` tail from `actualWeightedHighEnergy_le` under the selected ambient
   bound. `conservative_material_scalar_contradiction` gives `False`.

## Dependencies to pin in the eventual manifest

- Full113 input archive:
  `C:/Users/dfred/.quantyra/builder02/full113-exact-real-complex-operators-repair3-resource02/input-archive.tar.gz`,
  SHA256 `BE67B48A7D6AA2745A1D28B99953E29B5764686EECFE4EDCFA01908872DE7EC2`.
- Density bridge v2 source SHA256
  `642C3CA24DB6247C7797444BD02951173F43BA3249968EC40BFD8987A2898C7E`.
- Finite maximum / Boolean energy v2 source SHA256
  `C3F6EC5A18D923C7B415003944814541185638D7795A8B66995E6E3976EC7BD1`.
- Scalar v6 source SHA256
  `002998DCDBF10A2A145524078C6DA32545004D68C8A2AD45C2B34F6337B628FF`.
- Source-height v3 source SHA256
  `98661E33A9C272CB983368B60C12BF7AA7BE833076A5545CAB1CDF4917209BDF`.
- Explicit-height v3 source SHA256
  `B255244AE3D98413B943278A8C17E5099FAB876573E8E62A530093955D898847`.
- Exact-threshold v2 source SHA256
  `521BFC410764BF74582CA11CFC1E527224F90DC9D1C8441DAF344899A6D4C551`.

All listed candidates remain uncompiled. The exact source-member hashes for
the HC46/spectral inhabitants, weighted selector, and manuscript material
theorem must also be recorded in the completed manifest. Caller-supplied
source selector, cutoff, original table, sampler, and same-instance unconditioned
side-density remain explicit; no `hSignal`, `hXleBeta`, `hBetaLink`, or
material-RHS estimate is an external premise.
