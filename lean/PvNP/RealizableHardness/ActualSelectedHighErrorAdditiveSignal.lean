import Mathlib.Tactic
import PvNP.RealizableHardness.ActualSelectedHighErrorSignalComparison
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

/-! Scalar comparison from the genuine selected high-error estimate to a conservative source-shaped dyadic scale. This module proves only a scalar error budget; it asserts no equality between this scale and the actual selector signal. -/

namespace PvNP.RealizableHardness.ActualSelectedHighErrorAdditiveSignal

open PvNP.RealizableHardness.ActualSelectedHighErrorSignalComparison
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

set_option autoImplicit false
noncomputable section

def sourceAdditiveSignalExponent (m h : Nat) : Real :=
  -4 * (1 - 1000 * (fixedRho m : Real)) * (m : Real) * (h : Real) - 2 -
    (m : Real) * (leafK m h : Real)

private theorem leafK_eq_fixedRho_height {m h : Nat}
    (hm : 0 < m) (hdiv : bOf m ∣ h) :
    (leafK m h : Real) = 2 * (fixedRho m : Real) * (h : Real) := by
  have hK := ActualSelectedSpectralParameters.leafK_eq_two_mul_quotient hdiv
  have hqNat : bOf m * (h / bOf m) = h := by
    have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hdecomp := Nat.mod_add_div h (bOf m)
    rw [hmod] at hdecomp
    nlinarith [hdecomp]
  have hqR : (bOf m : Real) * ((h / bOf m : Nat) : Real) = (h : Real) := by
    exact_mod_cast hqNat
  have hrho := fixed_rho_explicit hm
  have hbR : (bOf m : Real) = 4000 * (m : Real) ^ 2 := by simp [bOf]
  rw [hK, hrho]
  push_cast
  field_simp [ne_of_gt (show (0 : Real) < (m : Real) by exact_mod_cast hm)]
  rw [← hqR, hbR]
  ring

/-- The exact source error sources are bounded by half of the conservative source-shaped dyadic scale. -/
theorem doubled_high_error_budget_le_additive_half {m h : Nat}
    (hm : 256 <= m) (hh : 20001 * m ^ 2 <= h)
    (hdiv : bOf m ∣ h) {beta : Real}
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1) :
    2 * ((2 : Real) * (2 : Real) ^ (-(sourceRankExponent m : Real) *
        ((leafK m h : Real) - 1)) /
        (manuscriptMomentThreshold m h) ^ 2 +
      (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m * beta) <=
      (2 : Real) ^ (sourceAdditiveSignalExponent m h) / 2 := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hmRlarge : (256 : Real) <= (m : Real) := by exact_mod_cast hm
  have hhR : 0 <= (h : Real) := by positivity
  have hrho := fixed_rho_explicit hmpos
  have hrhoPos : 0 < (fixedRho m : Real) := by rw [hrho]; positivity
  have hrhoLe : (fixedRho m : Real) <= 1 := by
    rw [hrho]
    have hden : 0 < 4000 * (m : Real) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [hmRlarge]
  have hrhoComplement : 0 <= 1 - (fixedRho m : Real) := sub_nonneg.mpr hrhoLe
  have hsReal := leafK_eq_fixedRho_height hmpos hdiv
  have hcompare : sourceWeightedSignalExponent m h <=
      sourceAdditiveSignalExponent m h - 3 := by
    unfold sourceWeightedSignalExponent sourceAdditiveSignalExponent
    rw [hsReal]
    have hleft : 0 <= 2 * (1 - (fixedRho m : Real)) * (h : Real) :=
      mul_nonneg (mul_nonneg (by norm_num) hrhoComplement) hhR
    have hright : 0 <= 2 * (m : Real) * (fixedRho m : Real) * (h : Real) :=
      mul_nonneg (mul_nonneg (by positivity) (le_of_lt hrhoPos)) hhR
    nlinarith [hleft, hright]
  have hgreen := doubled_high_error_budget_le_half hm hh hdiv hbeta0 hbeta1
  have hpow : (2 : Real) ^ (sourceWeightedSignalExponent m h) <=
      (2 : Real) ^ (sourceAdditiveSignalExponent m h - 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2) hcompare
  have hpowMon : (2 : Real) ^ (sourceAdditiveSignalExponent m h - 3) <=
      (2 : Real) ^ (sourceAdditiveSignalExponent m h) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2) (by linarith)
  calc
    _ <= (2 : Real) ^ (sourceWeightedSignalExponent m h) / 2 := hgreen
    _ <= (2 : Real) ^ (sourceAdditiveSignalExponent m h - 3) / 2 :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    _ <= (2 : Real) ^ (sourceAdditiveSignalExponent m h) / 2 :=
      div_le_div_of_nonneg_right hpowMon (by norm_num)

end
end PvNP.RealizableHardness.ActualSelectedHighErrorAdditiveSignal