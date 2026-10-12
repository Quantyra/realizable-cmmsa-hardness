import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
The manuscript-faithful arithmetic handoff for the CMMSA parameter family.

This module is deliberately independent of the unfinished outer carrier.  It
defines the exact natural-number blocks, the gap root used by the HN premise,
and the `/16`, `/4`, `/2` repair chain.  `hBlock` is a fixed-`L,m`
block-scale constructor, not an admissibility selector.  All outer-law,
amplification, materialization, and reduction statements remain conditional
and outside this module.
-/
namespace PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

def log2nat (n : Nat) : Nat := if n = 0 then 0 else Nat.log 2 n

def q (m : Nat) : Nat := Nat.sqrt m

def bOf (m : Nat) : Nat := 4000 * m ^ 2

def blockNum (L m : Nat) : Nat :=
  if L = 0 then 0 else (L - 1) / Nat.max (q m * (m + 1)) 1

/-- The fixed-`L,m` natural-number block-scale constructor. -/
def hBlock (L m : Nat) : Nat :=
  bOf m * (log2nat (blockNum L m) / (2 * bOf m))

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

theorem bOf_dvd_hBlock (L m : Nat) : bOf m ∣ hBlock L m := by
  dsimp [hBlock]
  exact dvd_mul_right _ _

theorem sigmaFinal_eq (L m : Nat) :
    sigmaFinal L m = (sigmaBase L m / 4) / 2 := rfl

theorem gammaFinal_eq (m : Nat) :
    gammaFinal m = 4 * ((3 / 4 : Rat) ^ q m) := by
  simp [gammaFinal, Gamma]
  ring

theorem two_mul_hBlock_le_log2_blockNum (L m : Nat) :
    2 * hBlock L m ≤ log2nat (blockNum L m) := by
  dsimp [hBlock]
  calc
    2 * (bOf m * (log2nat (blockNum L m) / (2 * bOf m))) =
        (2 * bOf m) * (log2nat (blockNum L m) / (2 * bOf m)) := by ring
    _ ≤ log2nat (blockNum L m) :=
      Nat.mul_div_le (log2nat (blockNum L m)) (2 * bOf m)

theorem RBlock_le_blockNum {L m : Nat} (hn : 0 < blockNum L m) :
    RBlock L m ≤ blockNum L m := by
  have hlog : 2 * hBlock L m ≤ log2nat (blockNum L m) :=
    two_mul_hBlock_le_log2_blockNum L m
  have hpow : 2 ^ (2 * hBlock L m) ≤ 2 ^ log2nat (blockNum L m) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hlog
  have hpowlog : 2 ^ log2nat (blockNum L m) ≤ blockNum L m := by
    rw [show log2nat (blockNum L m) = Nat.log 2 (blockNum L m) from
      ite_eq_right (Nat.ne_of_gt hn)]
    exact Nat.pow_log_le_self 2 hn.ne'
  have hR : RBlock L m ≤ 2 ^ log2nat (blockNum L m) := by
    simpa [RBlock] using hpow
  exact hR.trans hpowlog

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

/-- The amplified leaf budget follows from the exact block numerator. -/
theorem amplified_leaf_fit_of_hBlock
    {L m : Nat}
    (hm : 0 < m)
    (hden : q m * (m + 1) < L) :
    q m * (m + 1) * RBlock L m + 1 ≤ L := by
  let d := q m * (m + 1)
  have hq : 0 < q m := Nat.sqrt_pos.2 hm
  have hd : 0 < d := Nat.mul_pos hq (Nat.succ_pos m)
  have hdL : d < L := by simpa [d] using hden
  have hLpos : 0 < L := hd.trans hdL
  have hdle : d ≤ L - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt hdL)
  have hmax : Nat.max d 1 = d := Nat.max_eq_left (Nat.succ_le_iff.mp hd)
  have hnumpos : 0 < blockNum L m := by
    simp only [blockNum, ite_eq_right hLpos.ne']
    rw [hmax]
    exact Nat.div_pos hdle hd
  have hR : RBlock L m ≤ blockNum L m := RBlock_le_blockNum hnumpos
  have hmul : d * blockNum L m ≤ L - 1 := by
    have hblockNum_eq : blockNum L m = (L - 1) / Nat.max d 1 := by
      simp [blockNum, d, hLpos.ne']
    rw [hblockNum_eq, hmax]
    exact Nat.mul_div_le _ _
  have hmulR : d * RBlock L m ≤ d * blockNum L m :=
    Nat.mul_le_mul_left d hR
  have hsum : d * RBlock L m + 1 ≤ (L - 1) + 1 :=
    (Nat.add_le_add_right hmulR 1).trans (Nat.add_le_add_right hmul 1)
  have hsumL : d * RBlock L m + 1 ≤ L := by
    have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
    calc
      d * RBlock L m + 1 ≤ (L - 1) + 1 := hsum
      _ = L := Nat.sub_add_cancel hLone
  simpa [d] using hsumL

end PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
