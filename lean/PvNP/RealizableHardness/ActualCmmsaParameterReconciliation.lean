import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
The manuscript-faithful arithmetic handoff for the CMMSA parameter family.

This module is deliberately independent of the unfinished outer carrier.  It
defines the exact natural-number blocks, the gap root used by the HN premise,
and the `/16`, `/4`, `/2` repair chain.  It does not claim an outer score law,
an AND construction, a codec, a reduction, or a CMMSA promise theorem.
-/
namespace PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

def log2nat (n : Nat) : Nat := if n = 0 then 0 else Nat.log 2 n

def q (m : Nat) : Nat := Nat.sqrt m

def bOf (m : Nat) : Nat := 4000 * m ^ 2

/-- The exact natural-number block selector from the manuscript. -/
def hBlock (L m : Nat) : Nat :=
  let den := q m * (m + 1)
  let num := if L = 0 then 0 else (L - 1) / Nat.max den 1
  bOf m * (log2nat num / (2 * bOf m))

def RBlock (L m : Nat) : Nat := 2 ^ (2 * hBlock L m)

/-- `R^(1-1/m)` represented without real powers. -/
def gapRoot (L m : Nat) : Nat :=
  2 ^ (2 * (hBlock L m / m) * (m - 1))

def sigmaBase (L m : Nat) : Nat := gapRoot L m / 16

def sigmaRepair (L m : Nat) : Nat := sigmaBase L m / 4

def sigmaFinal (L m : Nat) : Nat := sigmaRepair L m / 2

def Gamma (m : Nat) : Rat := 2 * ((3 / 4 : Rat) ^ q m)

def gammaFinal (m : Nat) : Rat := 2 * Gamma m

def oldSigma (L m : Nat) : Nat := RBlock L m / 8

theorem m_dvd_bOf (m : Nat) : m ∣ bOf m := by
  refine ⟨4000 * m, ?_⟩
  simp [bOf, pow_two, Nat.mul_assoc, Nat.mul_comm]

theorem m_dvd_hBlock (L m : Nat) : m ∣ hBlock L m := by
  exact dvd_mul_of_dvd_left (m_dvd_bOf m) _

theorem sigmaFinal_eq (L m : Nat) :
    sigmaFinal L m = (sigmaBase L m / 4) / 2 := rfl

theorem gammaFinal_eq (m : Nat) :
    gammaFinal m = 4 * ((3 / 4 : Rat) ^ q m) := by
  simp [gammaFinal, Gamma]
  ring

private theorem cast_div16_of_dvd {a : Nat} (hd : 16 ∣ a) :
    ((a / 16 : Nat) : ℝ) = (a : ℝ) / 16 := by
  rw [Nat.cast_div hd (by norm_num)]
  norm_num

private theorem cast_div8_of_dvd {a : Nat} (hd : 8 ∣ a) :
    ((a / 8 : Nat) : ℝ) = (a : ℝ) / 8 := by
  rw [Nat.cast_div hd (by norm_num)]
  norm_num

private theorem pow_half_le_five_eighths (n : Nat) :
    ((1 / 2 : ℝ) ^ (n + 1)) ≤ (5 / 8 : ℝ) := by
  have hpow0 : ((1 / 2 : ℝ) ^ n) ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : ((1 / 2 : ℝ) ^ (n + 1)) ≤ (1 / 2 : ℝ) := by
    rw [pow_succ]
    nlinarith
  linarith

private theorem gap_power_cancel {g : ℝ} (hg : 0 < g) (n : Nat) :
    (g / 2) ^ n * (g ^ n)⁻¹ = ((1 / 2 : ℝ) ^ n) := by
  rw [div_pow]
  field_simp [ne_of_gt hg]
  rw [← mul_pow]
  norm_num

/-- The exact HN arithmetic handoff at the encoded gap-root endpoint. -/
theorem hn_handoff
    {L m : Nat} {zeta : ℝ}
    (_hm : 0 < m)
    (hgap_pos : 0 < gapRoot L m)
    (hgap16 : 16 ∣ gapRoot L m)
    (hzeta : zeta ≤ ((gapRoot L m : ℝ) ^ (m + 1))⁻¹) :
    (8 * (sigmaBase L m : ℝ)) ^ (m + 1) * zeta ≤ (5 / 8 : ℝ) := by
  have hsigma : (sigmaBase L m : ℝ) = (gapRoot L m : ℝ) / 16 := by
    simp only [sigmaBase]
    exact cast_div16_of_dvd hgap16
  have hfactor :
      (8 * (sigmaBase L m : ℝ)) ^ (m + 1) =
        ((gapRoot L m : ℝ) / 2) ^ (m + 1) := by
    rw [hsigma]
    congr 1
    ring
  rw [hfactor]
  have hnonneg : 0 ≤ ((gapRoot L m : ℝ) / 2) ^ (m + 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hzeta hnonneg
  have hgap_posR : 0 < (gapRoot L m : ℝ) := by exact_mod_cast hgap_pos
  have hcancel := gap_power_cancel (g := (gapRoot L m : ℝ)) hgap_posR (m + 1)
  rw [hcancel] at hmul
  exact hmul.trans (pow_half_le_five_eighths m)

/-- Symbolic witness that the legacy `R/8` route fails at the same endpoint. -/
theorem old_sigma_route_failure
    {L m : Nat}
    (_hm : 0 < m)
    (hgap_pos : 0 < gapRoot L m)
    (hR_pos : 0 < RBlock L m)
    (hR8 : 8 ∣ RBlock L m)
    (hgap_lt : gapRoot L m < RBlock L m) :
    (1 : ℝ) <
      (8 * (oldSigma L m : ℝ)) ^ (m + 1) *
        ((gapRoot L m : ℝ) ^ (m + 1))⁻¹ := by
  have hold : (oldSigma L m : ℝ) = (RBlock L m : ℝ) / 8 := by
    simp only [oldSigma]
    exact cast_div8_of_dvd hR8
  rw [hold]
  have hposG : 0 < (gapRoot L m : ℝ) := by exact_mod_cast hgap_pos
  have hltR : (gapRoot L m : ℝ) < (RBlock L m : ℝ) := by exact_mod_cast hgap_lt
  have hpowlt :
      (gapRoot L m : ℝ) ^ (m + 1) < (RBlock L m : ℝ) ^ (m + 1) := by
    gcongr
  have hpowpos : 0 < (gapRoot L m : ℝ) ^ (m + 1) := pow_pos hposG _
  have hratio :
      1 < (RBlock L m : ℝ) ^ (m + 1) /
        (gapRoot L m : ℝ) ^ (m + 1) := by
    exact (lt_div_iff₀ hpowpos).2 (by simpa using hpowlt)
  have hrewrite :
      (8 * ((RBlock L m : ℝ) / 8)) ^ (m + 1) *
          ((gapRoot L m : ℝ) ^ (m + 1))⁻¹ =
        (RBlock L m : ℝ) ^ (m + 1) /
          (gapRoot L m : ℝ) ^ (m + 1) := by
    field_simp
  rw [hrewrite]
  exact hratio

/-- The amplified leaf budget, with its exact natural-number sufficient bound. -/
theorem amplified_leaf_fit
    {L m : Nat}
    (hfit : q m * (m + 1) * 2 ^ (2 * hBlock L m) + 1 ≤ L) :
    q m * (m + 1) * RBlock L m + 1 ≤ L := by
  simpa [RBlock] using hfit

end PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
