import Mathlib.Tactic
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
import PvNP.RealizableHardness.ActualSelectedSpectralTailGeometry
import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

/-! Quantitative high-error comparison for the actual selected source tail.
This file handles only scalar exponent arithmetic: the all-level spectral sum
is supplied by the independent energy/tail theorem, and the selected-f signal
identity is left to the material caller. -/

namespace PvNP.RealizableHardness.ActualSelectedHighErrorSignalComparison

open PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
open PvNP.RealizableHardness.ActualSelectedSpectralTailGeometry
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

set_option autoImplicit false
noncomputable section

def sourceRankExponent (m : Nat) : Nat := 40000 * m ^ 3

def sourceHighErrorExponentGap (m h : Nat) : Real :=
  (((8 : Real) / 3) * (m : Real) - 2 +
      (3996 * (m : Real) + 2) * (fixedRho m : Real)) * (h : Real) -
    ((sourceRankExponent m : Real) + 7)

def sourceHighErrorExponent (m h : Nat) : Real :=
  (sourceRankExponent m : Real) + 2 -
    ((20 : Real) / 3) * (m : Real) * (h : Real)

def sourceWeightedSignalExponent (m h : Nat) : Real :=
  -4 * (1 - 1000 * (fixedRho m : Real)) * (m : Real) * (h : Real) - 5 -
    2 * (1 - (fixedRho m : Real)) * (h : Real) -
    4 * (m : Real) * (fixedRho m : Real) * (h : Real)

theorem source_signal_exponent_gap_exact {m h : Nat} :
    sourceWeightedSignalExponent m h - sourceHighErrorExponent m h =
      sourceHighErrorExponentGap m h := by
  unfold sourceWeightedSignalExponent sourceHighErrorExponent
    sourceHighErrorExponentGap sourceRankExponent
  ring

/-- The actual fixed-rho high error is separated from the selected weighted
signal exponent by at least three full powers of two. -/
theorem source_high_error_gap_ge_three {m h : Nat}
    (hm : 256 <= m) (hh : 20001 * m ^ 2 <= h) :
    3 <= sourceHighErrorExponentGap m h := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hmRlarge : (256 : Real) <= (m : Real) := by exact_mod_cast hm
  have hhR : 20001 * (m : Real) ^ 2 <= (h : Real) := by exact_mod_cast hh
  have hrho := ActualSelectedComplementAnalyticNumerics.fixed_rho_explicit hmpos
  have hrhoPos : 0 < (fixedRho m : Real) := by rw [hrho]; positivity
  have hcoeff :
      2 * (m : Real) <= (8 / 3 : Real) * (m : Real) - 2 +
        (3996 * (m : Real) + 2) * (fixedRho m : Real) := by
    have hbase : 2 * (m : Real) <= (8 / 3 : Real) * (m : Real) - 2 := by
      nlinarith
    exact hbase.trans (by
      nlinarith [mul_nonneg
        (show 0 <= 3996 * (m : Real) + 2 by positivity)
        (show 0 <= (fixedRho m : Real) by exact hrhoPos.le)])
  have hrNat : (sourceRankExponent m : Real) = 40000 * (m : Real) ^ 3 := by
    norm_num [sourceRankExponent, pow_succ]
  have hmge2 : 2 <= m := by omega
  have hmsqNat : 4 <= m ^ 2 := by
    calc
      4 = 2 * 2 := by norm_num
      _ <= m * m := Nat.mul_le_mul hmge2 hmge2
      _ = m ^ 2 := by rw [pow_two]
  have hmcubeNat : 8 <= m ^ 3 := by
    calc
      8 = 4 * 2 := by norm_num
      _ <= m ^ 2 * m := Nat.mul_le_mul hmsqNat hmge2
      _ = m ^ 3 := by norm_num [pow_succ, pow_two]
  have hmcube : (8 : Real) <= (m : Real) ^ 3 := by exact_mod_cast hmcubeNat
  have hmain : 40000 * (m : Real) ^ 3 + 10 <= 40002 * (m : Real) ^ 3 := by
    nlinarith [hmcube]
  unfold sourceHighErrorExponentGap
  rw [hrNat]
  have hcoeffMul := mul_le_mul_of_nonneg_right hcoeff
    (show 0 <= (h : Real) by positivity)
  have hheightMul := mul_le_mul_of_nonneg_left hhR
    (show 0 <= 2 * (m : Real) by positivity)
  have hmul : 2 * (m : Real) * (20001 * (m : Real) ^ 2) =
      40002 * (m : Real) ^ 3 := by ring
  nlinarith [hcoeffMul, hheightMul, hmul, hmain]

private theorem leafK_eq_fixedRho_height {m h : Nat}
    (hm : 0 < m) (hdiv : bOf m ∣ h) :
    (leafK m h : Real) = 2 * (fixedRho m : Real) * (h : Real) := by
  have hK : leafK m h = 2 * (h / bOf m) :=
    ActualSelectedSpectralParameters.leafK_eq_two_mul_quotient hdiv
  have hqNat : bOf m * (h / bOf m) = h := by
    have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hdecomp := Nat.mod_add_div h (bOf m)
    rw [hmod] at hdecomp
    nlinarith [hdecomp]
  have hqR : (bOf m : Real) * ((h / bOf m : Nat) : Real) = (h : Real) := by
    exact_mod_cast hqNat
  have hrho := ActualSelectedComplementAnalyticNumerics.fixed_rho_explicit hm
  have hbR : (bOf m : Real) = 4000 * (m : Real) ^ 2 := by simp [bOf]
  rw [hK, hrho]
  push_cast
  field_simp [ne_of_gt (show (0 : Real) < (m : Real) by exact_mod_cast hm)]
  rw [← hqR, hbR]
  ring

private theorem manuscript_threshold_eq_dyadic {m h : Nat} (hm : 0 < m) :
    manuscriptMomentThreshold m h =
      (2 : Real) ^ (-((20 : Real) / 3) * (m : Real) * (h : Real)) :=
  manuscript_threshold_simplifies hm

private theorem dyadic_mul_exp {x y : Real} :
    (2 : Real) ^ x * (2 : Real) ^ y = (2 : Real) ^ (x + y) := by
  rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]

private theorem dyadic_two_mul_exp {x : Real} :
    2 * (2 : Real) ^ x = (2 : Real) ^ (1 + x) := by
  calc
    2 * (2 : Real) ^ x = (2 : Real) ^ (1 : Real) * (2 : Real) ^ x := by
      rw [Real.rpow_one]
    _ = (2 : Real) ^ (1 + x) := dyadic_mul_exp

private theorem dyadic_power_square {x : Real} :
    ((2 : Real) ^ x) ^ 2 = (2 : Real) ^ (2 * x) := by
  rw [← Real.rpow_natCast ((2 : Real) ^ x) 2]
  rw [Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  rw [show x * (2 : Real) = 2 * x by ring]

private theorem dyadic_div_eighth {x : Real} :
    (2 : Real) ^ x / 8 = (2 : Real) ^ (x - 3) := by
  rw [show (8 : Real) = (2 : Real) ^ (3 : Real) by norm_num,
    div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : Real) <= 2),
    dyadic_mul_exp]
  rw [show x + -3 = x - 3 by ring]

/-- The actual spectral high term is bounded by the conservative error
exponent; the i-dependent second tail term is handled upstream by the genuine
all-level energy theorem and is not replaced here. -/
theorem spectral_high_error_le_dyadic {m h : Nat}
    (hm : 256 <= m) (hh : 20001 * m ^ 2 <= h)
    (hdiv : bOf m ∣ h) :
    2 * (2 : Real) ^ (-(sourceRankExponent m : Real) *
        ((leafK m h : Real) - 1)) /
        (manuscriptMomentThreshold m h) ^ 2 <=
      (2 : Real) ^ (sourceWeightedSignalExponent m h) / 8 := by
  have hmpos : 0 < m := by omega
  have hK := leafK_eq_fixedRho_height hmpos hdiv
  have hrho := ActualSelectedComplementAnalyticNumerics.fixed_rho_explicit hmpos
  have hrNat : (sourceRankExponent m : Real) = 40000 * (m : Real) ^ 3 := by
    norm_num [sourceRankExponent, pow_succ]
  have hrhoRank : (sourceRankExponent m : Real) * (fixedRho m : Real) =
      10 * (m : Real) := by
    rw [hrNat, hrho]
    field_simp [ne_of_gt (show (0 : Real) < (m : Real) by exact_mod_cast hmpos)]
    ring
  have hscaledRank : (sourceRankExponent m : Real) *
      (2 * (fixedRho m : Real) * (h : Real)) =
        20 * (m : Real) * (h : Real) := by
    calc
      (sourceRankExponent m : Real) *
          (2 * (fixedRho m : Real) * (h : Real)) =
        2 * ((sourceRankExponent m : Real) * (fixedRho m : Real)) * (h : Real) := by ring
      _ = 2 * (10 * (m : Real)) * (h : Real) := by rw [hrhoRank]
      _ = 20 * (m : Real) * (h : Real) := by ring
  have ha := manuscript_threshold_eq_dyadic (m := m) (h := h) hmpos
  have ha2 : (manuscriptMomentThreshold m h) ^ 2 =
      (2 : Real) ^ (2 * (-((20 : Real) / 3) * (m : Real) * (h : Real))) := by
    rw [ha, dyadic_power_square]
  have hspecEq :
      2 * (2 : Real) ^ (-(sourceRankExponent m : Real) *
          ((leafK m h : Real) - 1)) /
          (manuscriptMomentThreshold m h) ^ 2 =
        (2 : Real) ^ (sourceHighErrorExponent m h - 1) := by
    have hdenInv :
        ((2 : Real) ^ (2 * (-((20 : Real) / 3) * (m : Real) * (h : Real))))⁻¹ =
          (2 : Real) ^ (-(2 * (-((20 : Real) / 3) * (m : Real) * (h : Real)))) := by
      rw [← Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
    calc
      2 * (2 : Real) ^ (-(sourceRankExponent m : Real) *
          ((leafK m h : Real) - 1)) /
          (manuscriptMomentThreshold m h) ^ 2 =
          2 * (2 : Real) ^ (-(sourceRankExponent m : Real) *
            ((leafK m h : Real) - 1)) *
            (2 : Real) ^ (-(2 * (-((20 : Real) / 3) * (m : Real) * (h : Real)))) := by
              rw [ha2, div_eq_mul_inv, hdenInv]
      _ = (2 : Real) ^ (1 + (-(sourceRankExponent m : Real) *
            ((leafK m h : Real) - 1)) +
            (-(2 * (-((20 : Real) / 3) * (m : Real) * (h : Real))))) := by
              rw [dyadic_two_mul_exp, dyadic_mul_exp]
      _ = (2 : Real) ^ (sourceHighErrorExponent m h - 1) := by
        apply congrArg (fun e : Real => (2 : Real) ^ e)
        unfold sourceHighErrorExponent
        rw [hK, hscaledRank]
        ring
  have hgap := source_high_error_gap_ge_three hm hh
  have hgapExact := source_signal_exponent_gap_exact (m := m) (h := h)
  have hsignalExponent : sourceHighErrorExponent m h - 1 <=
      sourceWeightedSignalExponent m h - 3 := by
    linarith [hgap, hgapExact]
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : Real) <= 2) hsignalExponent
  rw [hspecEq]
  rw [show (8 : Real) = (2 : Real) ^ (3 : Real) by norm_num]
  rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
  rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
  simpa only [show sourceWeightedSignalExponent m h - 3 =
      sourceWeightedSignalExponent m h + (-3) by ring] using hpow

/-- The genuine threshold high term is also at most one eighth of the same
weighted signal scale whenever the actual beta lies in [0,1]. -/
theorem threshold_high_error_le_dyadic {m h : Nat} (hm : 256 <= m)
    (hh : 20001 * m ^ 2 <= h) {beta : Real}
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1) :
    (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m * beta <=
      (2 : Real) ^ (sourceWeightedSignalExponent m h) / 8 := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hmRlarge : (256 : Real) <= (m : Real) := by exact_mod_cast hm
  have hhR : 20001 * (m : Real) ^ 2 <= (h : Real) := by exact_mod_cast hh
  have hrho := ActualSelectedComplementAnalyticNumerics.fixed_rho_explicit hmpos
  have hrhoPos : 0 < (fixedRho m : Real) := by rw [hrho]; positivity
  have hrhoCoeff : 4 * (m : Real) * (fixedRho m : Real) <= 1 := by
    rw [hrho]
    have hmSq : 1 <= (m : Real) ^ 2 := by nlinarith
    have hnz : (m : Real) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hnz]
    nlinarith [hmSq]
  have hweightedLower :
      -4 * (m : Real) * (h : Real) - 3 * (h : Real) - 5 <=
        sourceWeightedSignalExponent m h := by
    unfold sourceWeightedSignalExponent
    have ht1 : 0 <= 4000 * (m : Real) * (fixedRho m : Real) * (h : Real) := by positivity
    have ht2 : 0 <= 2 * (fixedRho m : Real) * (h : Real) := by positivity
    have ht3 : 0 <= (1 - 4 * (m : Real) * (fixedRho m : Real)) * (h : Real) :=
      mul_nonneg (by linarith [hrhoCoeff]) (by positivity)
    nlinarith [ht1, ht2, ht3]
  have hcoef : 4 * (m : Real) + 4 <= (20 / 3 : Real) * (m : Real) ^ 2 := by
    nlinarith [hmRlarge]
  have hcoefMul := mul_le_mul_of_nonneg_right hcoef (show 0 <= (h : Real) by positivity)
  have hhlarge : (m : Real) + 8 <= (h : Real) := by nlinarith [hhR, hmRlarge]
  have hexp :
      (m : Real) - (20 / 3 : Real) * (m : Real) ^ 2 * (h : Real) <=
        sourceWeightedSignalExponent m h - 3 := by
    have hdom :
        (4 * (m : Real) + 3) * (h : Real) + (m : Real) + 8 <=
          (20 / 3 : Real) * (m : Real) ^ 2 * (h : Real) := by
      nlinarith [hcoefMul, hhlarge]
    linarith [hdom, hweightedLower]
  have ha := manuscript_threshold_eq_dyadic (m := m) (h := h) hmpos
  have haPos : 0 < manuscriptMomentThreshold m h := by
    rw [ha]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have haPow : (manuscriptMomentThreshold m h) ^ m =
      (2 : Real) ^ ((-((20 : Real) / 3) * (m : Real) * (h : Real)) *
        (m : Real)) := by
    rw [ha]
    rw [← Real.rpow_natCast ((2 : Real) ^
      (-((20 : Real) / 3) * (m : Real) * (h : Real))) h]
    rw [Real.rpow_mul (by positivity)]
    rw [← Real.rpow_natCast (2 : Real) m]
    rw [Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
    congr 1
    ring
  have hprod :
      (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m =
        (2 : Real) ^ ((m : Real) - (20 / 3 : Real) *
          (m : Real) ^ 2 * (h : Real)) := by
    calc
      (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m =
          (2 : Real) ^ (m : Real) *
            (2 : Real) ^ ((-((20 : Real) / 3) * (m : Real) * (h : Real)) * (m : Real)) := by
        rw [haPow]
      _ = (2 : Real) ^ ((m : Real) +
          ((-((20 : Real) / 3) * (m : Real) * (h : Real)) * (m : Real))) :=
        dyadic_mul_exp
      _ = (2 : Real) ^ ((m : Real) - (20 / 3 : Real) *
          (m : Real) ^ 2 * (h : Real)) := by
        rw [show (m : Real) +
          ((-((20 : Real) / 3) * (m : Real) * (h : Real)) * (m : Real)) =
            (m : Real) - (20 / 3 : Real) * (m : Real) ^ 2 * (h : Real) by ring]
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : Real) <= 2) hexp
  have hscaled :
      (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m <=
        (2 : Real) ^ (sourceWeightedSignalExponent m h - 3) := by
    rw [hprod]
    exact hpow
  have hfactorNonneg : 0 <= (2 : Real) ^ (m : Real) *
      (manuscriptMomentThreshold m h) ^ m := by positivity
  have hbeta := mul_le_mul_of_nonneg_left hbeta1 hfactorNonneg
  calc
    (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m * beta <=
        (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m := by
          exact hbeta
    _ <= (2 : Real) ^ (sourceWeightedSignalExponent m h - 3) := by
      rw [hprod]
      exact hpow
    _ = (2 : Real) ^ (sourceWeightedSignalExponent m h) / 8 :=
      (dyadic_div_eighth (x := sourceWeightedSignalExponent m h)).symm

/-- The two independent actual high-error sources consume at most half of
the same weighted signal exponent after the outer factor two in the source
comparison. -/
theorem doubled_high_error_budget_le_half {m h : Nat} (hm : 256 <= m)
    (hh : 20001 * m ^ 2 <= h) (hdiv : bOf m ∣ h) {beta : Real}
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1) :
    2 * ((2 : Real) * (2 : Real) ^ (-(sourceRankExponent m : Real) *
        ((leafK m h : Real) - 1)) /
        (manuscriptMomentThreshold m h) ^ 2 +
      (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m * beta) <=
      (2 : Real) ^ (sourceWeightedSignalExponent m h) / 2 := by
  have hspec := spectral_high_error_le_dyadic hm hh hdiv
  have hthreshold := threshold_high_error_le_dyadic hm hh hbeta0 hbeta1
  have hsum := add_le_add hspec hthreshold
  have hscaled := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : Real) <= 2)
  calc
    2 * ((2 : Real) * (2 : Real) ^ (-(sourceRankExponent m : Real) *
        ((leafK m h : Real) - 1)) /
        (manuscriptMomentThreshold m h) ^ 2 +
      (2 : Real) ^ (m : Real) * (manuscriptMomentThreshold m h) ^ m * beta) <=
        2 * ((2 : Real) ^ (sourceWeightedSignalExponent m h) / 8 +
          (2 : Real) ^ (sourceWeightedSignalExponent m h) / 8) := hscaled
    _ = (2 : Real) ^ (sourceWeightedSignalExponent m h) / 2 := by ring

end
end PvNP.RealizableHardness.ActualSelectedHighErrorSignalComparison
