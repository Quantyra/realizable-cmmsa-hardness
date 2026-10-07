import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector

/-! Exact arithmetic identification of the manuscript's real success scale
with the existing rational `successMargin` exponent. The rational rho is the
intended reciprocal block scale, and divisibility is retained explicitly. -/

namespace PvNP.RealizableHardness.ActualManuscriptComplementMargin

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualStarAcceptedGoodMass
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector

noncomputable section

/-- The manuscript's displayed real scale, with its actual real exponent. -/
def manuscriptSuccessScale (rho : ℚ) (m h : Nat) : ℝ :=
  (1 / 2 : ℝ) ^ (2 * (1 - 1000 * (rho : ℝ)) * (h : ℝ) * (m : ℝ))

/-- The actual fixed-rho parameter from the selector source. -/
def manuscriptRho (m : Nat) : ℚ := fixedRho m

/-- Under the manuscript's exact reciprocal rho and admissible divisibility,
the real displayed scale is precisely the existing natural-exponent margin. -/
theorem manuscriptSuccessScale_eq_successMargin
    {m h : Nat} (hm : 0 < m) (hdiv : bOf m ∣ h) :
    manuscriptSuccessScale (manuscriptRho m) m h =
      (successMargin (badExponent m h) : ℝ) := by
  let q : Nat := h / bOf m
  have hbpos : 0 < bOf m := by
    dsimp [bOf]
    positivity
  have hbne : (bOf m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbpos)
  have hmul : bOf m * q = h := by
    dsimp [q]
    exact Nat.mul_div_cancel' hdiv
  have hb1000 : 1000 ≤ bOf m := by
    dsimp [bOf]
    have hm1 : 1 ≤ m := by omega
    have hsquare : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m hm1
    nlinarith
  have hsub : 1000 * q ≤ h := by
    calc
      1000 * q ≤ bOf m * q := Nat.mul_le_mul_right q hb1000
      _ = h := hmul
  have hcastmul : (h : ℝ) = (bOf m : ℝ) * (q : ℝ) := by
    exact_mod_cast hmul.symm
  have hrho : (manuscriptRho m : ℝ) = 1 / (bOf m : ℝ) := by
    change (fixedRho m : ℝ) = 1 / (bOf m : ℝ)
    exact_mod_cast fixedRho_eq_inverse_bOf hm
  have hexp :
      2 * (1 - 1000 * (manuscriptRho m : ℝ)) * (h : ℝ) * (m : ℝ) =
        (badExponent m h : ℝ) := by
    rw [hrho, hcastmul]
    have hcastsub : ((h - 1000 * q : Nat) : ℝ) =
        (h : ℝ) - 1000 * (q : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using Nat.cast_sub hsub
    have hbadexp : (badExponent m h : ℝ) =
        2 * (m : ℝ) * ((h - 1000 * q : Nat) : ℝ) := by
      unfold badExponent
      rw [show h / bOf m = q from rfl]
      push_cast
      rw [Nat.cast_sub hsub]
      ring
    rw [hbadexp, hcastsub, hcastmul]
    field_simp [hbne]
    ring
  rw [manuscriptSuccessScale, hexp, Real.rpow_natCast]
  simp [successMargin, Rat.cast_div, Rat.cast_pow]

/-- The initial manuscript choice `q = 8S` discharges the selector's
success-margin comparison without identifying arbitrary later q values. -/
theorem eight_mul_scale_margin_le_half
    {m h : Nat} (hm : 0 < m) (hdiv : bOf m ∣ h) :
    (successMargin (badExponent m h) : ℝ) ≤
      (8 : ℝ) * manuscriptSuccessScale (manuscriptRho m) m h / 2 := by
  rw [manuscriptSuccessScale_eq_successMargin hm hdiv]
  have hspos : 0 ≤ (successMargin (badExponent m h) : ℝ) := by
    positivity
  nlinarith

/-- The manuscript's initial rational threshold `8S` is exactly the cast of
eight times the accepted natural-exponent margin. -/
theorem rat_eight_margin_eq_eight_scale
    {m h : Nat} (hm : 0 < m) (hdiv : bOf m ∣ h) :
    ((8 * successMargin (badExponent m h) : ℚ) : ℝ) =
      8 * manuscriptSuccessScale (manuscriptRho m) m h := by
  rw [manuscriptSuccessScale_eq_successMargin hm hdiv]
  norm_num [Rat.cast_mul]

/-- The later robust-decoder input remains arbitrary: a separately proved
`q ≥ 4S` is enough to discharge its `successMargin ≤ q/2` premise. -/
theorem margin_le_half_of_four_scale_le
    {m h : Nat} (hm : 0 < m) (hdiv : bOf m ∣ h) {q : ℝ}
    (hq : 4 * manuscriptSuccessScale (manuscriptRho m) m h ≤ q) :
    (successMargin (badExponent m h) : ℝ) ≤ q / 2 := by
  rw [manuscriptSuccessScale_eq_successMargin hm hdiv] at hq
  nlinarith

end
end PvNP.RealizableHardness.ActualManuscriptComplementMargin
