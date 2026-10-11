# Exact selected-exponent transport: proof and API map

## Scope and claim boundary

This offer translates only the exact selected-exponent transport from the planning section “2026-10-10 Exact selected-density lower-signal argument.” It proves (1) the natural exponent casts to its fixed-rho real expression and (2) the rational `successMargin` at that exponent casts to the stated real power. It does not prove same-complement density averaging, weighted selection, a source instance/table witness, an actual global density bound, or a compiler/provider result. There is no rounding, floor, ceiling, or strengthened density hypothesis in either theorem.

## Public theorem profiles, stated before their proof dependencies

In `PvNP.RealizableHardness.ActualNumericExactThreshold`:

```lean
theorem badExponent_cast_eq_fixedRho {m h : Nat}
    (hm : 256 ≤ m) (hdiv : bOf m ∣ h) :
    (badExponent m h : Real) =
      2 * (1 - 1000 * (1 / (bOf m : Real))) * (m : Real) * (h : Real)

theorem successMargin_badExponent_cast_eq_selectedPower {m h : Nat}
    (hm : 256 ≤ m) (hdiv : bOf m ∣ h) :
    ((successMargin (badExponent m h) : ℚ) : Real) =
      Real.rpow 2
        (-(2 * (1 - 1000 * (1 / (bOf m : Real))) * (m : Real) * (h : Real)))
```

The first theorem uses only the requested hypotheses. `hm` establishes `bOf m ≥ 1000`, so the natural subtraction in `badExponent` casts exactly. Divisibility supplies `h = bOf m * (h / bOf m)`, identifying the quotient with `h / bOf m` over `Real`; field normalization then gives the fixed-rho identity. The second theorem first casts `successMargin E = 1 / (2:ℚ)^E` to `1 / (2:Real)^E`, applies pinned `Real.rpow_neg` and `Real.rpow_natCast`, and substitutes the first identity in the exponent.

The source-rho API is also proved directly. actualSelectedRho_eq_fixedRho_of_dvd_pos uses leafK_eq_two_mul_quotient and divisibility to identify the existing quotient definition with 1 / bOf m at positive heights. badExponent_cast_eq_actualSelectedRho and successMargin_badExponent_cast_eq_actualSelectedPower state the corresponding identities using that repository definition. Their additional 0 < h premise is only for the existing leafK/(2*h) quotient representation; selected_spectral_parameters already supplies it at its selected output. The fixed-rho theorems retain only the requested m >= 256 and divisibility assumptions, including h = 0.

## Existing rho API mapping

Pinned source `ActualSelectedSpectralParameters.lean` defines

```lean
def actualSelectedRho (m h : Nat) : Real :=
  (leafK m h : Real) / (2 * (h : Real))
```

and `selected_spectral_parameters` proves, at the actual selected positive `hBlock L m`, that `actualSelectedRho m hBlock = 1 / (bOf m : Real)`. The exact theorem above uses that established fixed-rho value explicitly. Its weaker hypotheses do not require positive `h`: this matters because `actualSelectedRho` is a ratio with a totalized zero denominator at `h = 0`, while the fixed-rho exponent identity itself remains valid there. The selector caller can replace the fixed ratio by `actualSelectedRho` using `selected_spectral_parameters`; no second, stronger assumption is added to the transport theorem.

## Dependency and argument map

- `ActualCmmsaParameterReconciliation.bOf`: `bOf m = 4000*m^2`. Its positive lower bound gives `bOf m ≥ 1000` from `m ≥ 256`.
- `ActualStarFixedRhoDimensionGuard.badExponent`: `2*m*(h - 1000*(h / bOf m))`. `bOf m ∣ h` provides the exact quotient decomposition and enough room for the natural subtraction.
- `ActualStarAcceptedGoodMass.successMargin`: `1/(2:ℚ)^E`. The pinned real-power identities identify its cast with `Real.rpow 2 (-(E:Real))`.
- `ActualSelectedSpectralParameters.actualSelectedRho` and `.selected_spectral_parameters`: identifies the fixed-rho expression with the selected namespace's rho at the selected positive height.
- Mathlib `Real.rpow_neg` and `Real.rpow_natCast` are the exact APIs used for the inverse natural power.

The next integration step, separately assigned, supplies the same rational threshold to the exact same selected complement. This offer does not imply that the averaging or weighted caller has been proved.

## Status

Source and Checks are developmental and uncompiled. Static UTF-8, BOM, glyph, and delimiter checks are reported in the manifest. No Lean, Lake, cloud, or Git command was run for this offer.
