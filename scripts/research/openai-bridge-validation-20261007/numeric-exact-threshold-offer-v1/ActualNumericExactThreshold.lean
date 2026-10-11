import Mathlib.Tactic
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

/-! Exact transport from the selected natural exponent to the real success scale.
This file proves only the exponent identity and rational-to-real power identity.
-/

namespace PvNP.RealizableHardness.ActualNumericExactThreshold

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.ActualStarAcceptedGoodMass
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

/-- The natural exponent has the exact fixed-rho real value whenever the
selected block is divisible by `bOf m`; no floor or ceiling is used. -/
theorem badExponent_cast_eq_fixedRho {m h : Nat}
    (hm : 256 ≤ m) (hdiv : bOf m ∣ h) :
    (badExponent m h : Real) =
      2 * (1 - 1000 * (1 / (bOf m : Real))) * (m : Real) * (h : Real) := by
  let q := h / bOf m
  have hmpos : 0 < m := by omega
  have hbpos : 0 < bOf m := by
    dsimp [bOf]
    positivity
  have hb1000 : 1000 ≤ bOf m := by
    dsimp [bOf]
    have hmSq : 1 ≤ m ^ 2 := by nlinarith
    nlinarith
  have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hdecomp : bOf m * q = h := by
    dsimp [q]
    have hdecomp' := Nat.mod_add_div h (bOf m)
    rw [hmod] at hdecomp'
    simpa [Nat.mul_comm] using hdecomp'
  have hsub : 1000 * q ≤ h := by
    calc
      1000 * q ≤ bOf m * q := Nat.mul_le_mul_right q hb1000
      _ = h := hdecomp
  have hbne : (bOf m : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbpos)
  have hdecompR : (h : Real) = (bOf m : Real) * (q : Real) := by
    exact_mod_cast hdecomp.symm
  have hqcast : (q : Real) = (h : Real) / (bOf m : Real) := by
    rw [hdecompR]
    field_simp [hbne] <;> ring
  unfold badExponent
  simp only [Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_ofNat]
  calc
    2 * (m : Real) * ((h : Real) - 1000 * (q : Real)) =
        2 * (m : Real) * ((h : Real) - 1000 * ((h : Real) / (bOf m : Real))) := by
          rw [hqcast]
    _ = 2 * (1 - 1000 * (1 / (bOf m : Real))) * (m : Real) * (h : Real) := by
          field_simp [hbne] <;> ring

/-- The exact rational `successMargin` at `badExponent` casts to the real
power scale selected by the fixed-rho argument. -/
theorem successMargin_badExponent_cast_eq_selectedPower {m h : Nat}
    (hm : 256 ≤ m) (hdiv : bOf m ∣ h) :
    ((successMargin (badExponent m h) : ℚ) : Real) =
      Real.rpow 2
        (-(2 * (1 - 1000 * (1 / (bOf m : Real))) * (m : Real) * (h : Real))) := by
  calc
    ((successMargin (badExponent m h) : ℚ) : Real) =
        1 / (2 : Real) ^ (badExponent m h) := by
          simp [successMargin]
    _ = Real.rpow 2 (-((badExponent m h : Nat) : Real)) := by
          rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2) ((badExponent m h : Nat) : Real)]
          rw [Real.rpow_natCast]
          simp [one_div]
    _ = Real.rpow 2
          (-(2 * (1 - 1000 * (1 / (bOf m : Real))) * (m : Real) * (h : Real))) := by
          congr 1
          rw [← badExponent_cast_eq_fixedRho hm hdiv]

 /-- The repository's selected-rho definition is exactly the fixed ratio at
positive divisible heights. Positivity is needed only because the existing
`actualSelectedRho` is represented as a quotient by `2*h`. -/
theorem actualSelectedRho_eq_fixedRho_of_dvd_pos {m h : Nat}
    (hdiv : bOf m ∣ h) (hh : 0 < h) :
    actualSelectedRho m h = 1 / (bOf m : Real) := by
  have hbpos : 0 < bOf m := by
    dsimp [bOf]
    positivity
  have hbne : (bOf m : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbpos)
  have hhR : (h : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hh)
  have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hdecomp : bOf m * (h / bOf m) = h := by
    have hd := Nat.mod_add_div h (bOf m)
    rw [hmod] at hd
    simpa [Nat.mul_comm] using hd
  have hdecompR : (bOf m : Real) * ((h / bOf m : Nat) : Real) = (h : Real) := by
    exact_mod_cast hdecomp
  unfold actualSelectedRho
  rw [leafK_eq_two_mul_quotient hdiv]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hhR, hbne] <;> nlinarith [hdecompR]

/-- The same exponent transport written with the existing selected-rho API.
At a selector output the positive-height premise is already part of
`selected_spectral_parameters`. -/
theorem badExponent_cast_eq_actualSelectedRho {m h : Nat}
    (hm : 256 ≤ m) (hdiv : bOf m ∣ h) (hh : 0 < h) :
    (badExponent m h : Real) =
      2 * (1 - 1000 * actualSelectedRho m h) * (m : Real) * (h : Real) := by
  rw [badExponent_cast_eq_fixedRho hm hdiv,
    actualSelectedRho_eq_fixedRho_of_dvd_pos hdiv hh]

/-- The exact rational success scale can likewise be stated using the
repository's selected-rho value at a positive divisible height. -/
theorem successMargin_badExponent_cast_eq_actualSelectedPower {m h : Nat}
    (hm : 256 ≤ m) (hdiv : bOf m ∣ h) (hh : 0 < h) :
    ((successMargin (badExponent m h) : ℚ) : Real) =
      Real.rpow 2 (-(2 * (1 - 1000 * actualSelectedRho m h) *
        (m : Real) * (h : Real))) := by
  rw [successMargin_badExponent_cast_eq_selectedPower hm hdiv,
    actualSelectedRho_eq_fixedRho_of_dvd_pos hdiv hh]

end PvNP.RealizableHardness.ActualNumericExactThreshold

