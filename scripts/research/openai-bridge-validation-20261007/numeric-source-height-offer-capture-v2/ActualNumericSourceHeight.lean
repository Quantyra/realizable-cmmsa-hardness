import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.SamplerParameters
import Mathlib.Tactic

/-! The explicit height floor for the numeric NO tail. Every selector premise
uses the enlarged base itself; no witness at an earlier base is transported.
Selector existence, the common effective cutoff and the source signal remain
separate obligations. This file is an uncompiled source candidate. -/
namespace PvNP.RealizableHardness.ActualNumericSourceHeight

open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualStarFixedRhoDimensionGuard ActualSelectedSpectralParameters
open SamplerParameters

set_option autoImplicit false

def numericRankThreshold (m : Nat) : Nat := 10 * m * bOf m

def numericSourceBase (base : Nat → Nat) (m : Nat) : Nat :=
  max (base m) (numericRankThreshold m)

theorem selected_numeric_height
    (base : Nat → Nat) (cutoff : Real → Nat) {L m : Nat}
    (hsel : selector
      (fun j => max (analyticSourceHeightFloor (numericSourceBase base) cutoff j) (j + 2)) L =
        (m : WithBot Nat)) :
    256 ≤ m ∧ numericRankThreshold m ≤ hBlock L m ∧
      base m ≤ hBlock L m ∧ cutoff (actualSelectedRho m (hBlock L m)) ≤ hBlock L m ∧
      bOf m ∣ hBlock L m := by
  rcases selected_spectral_parameters (numericSourceBase base) cutoff hsel with
    ⟨hm, _, hdiv, _, _, _, _, _, _, _, hbase, hcut⟩
  have hrank : numericRankThreshold m ≤ hBlock L m :=
    (Nat.le_max_right (base m) (numericRankThreshold m)).trans hbase
  have horiginal : base m ≤ hBlock L m :=
    (Nat.le_max_left (base m) (numericRankThreshold m)).trans hbase
  exact ⟨hm, hrank, horiginal, hcut, hdiv⟩

theorem fixed_numeric_tail_parameters
    {m h A : Nat} (hm : 2 ≤ m)
    (hrank : numericRankThreshold m ≤ h) (hdiv : bOf m ∣ h) (hA : 1 ≤ A) :
    20 * m ≤ leafK m h ∧ 1 ≤ leafK m h - 1 ∧
      leafT m h + leafK m h + numericRankThreshold m * (leafK m h - 1) + 3 ≤
        2 * blocks A h := by
  let b := bOf m
  let q := h / b
  have hmpos : 0 < m := by omega
  have hmsq : m ≤ m ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_left m hmpos
  have hb4000 : 4000 ≤ b := by
    dsimp [b, bOf]
    nlinarith [hmsq]
  have hbpos : 0 < b := by omega
  have hmod : h % b = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hdecomp : b * q = h := by
    have hmoddiv := Nat.mod_add_div h b
    rw [hmod] at hmoddiv
    simpa [q] using hmoddiv
  have hrank' : 10 * m * b ≤ h := hrank
  have hq : 10 * m ≤ q := by
    by_contra hbad
    have hqbad : q + 1 ≤ 10 * m := by omega
    have hproduct := Nat.mul_le_mul_left b hqbad
    nlinarith [hproduct, hdecomp]
  have hs : leafK m h = 2 * q := leafK_eq_two_mul_quotient hdiv
  have hslarge : 20 * m ≤ leafK m h := by
    rw [hs]
    omega
  have hsone : 1 ≤ leafK m h - 1 := by omega
  have hfull : numericRankThreshold m * leafK m h = 20 * m * h := by
    change 10 * m * b * leafK m h = 20 * m * h
    rw [hs]
    calc
      10 * m * b * (2 * q) = 20 * m * (b * q) := by ring
      _ = 20 * m * h := by rw [hdecomp]
  have htail : numericRankThreshold m * (leafK m h - 1) ≤ 20 * m * h := by
    have hle := Nat.mul_le_mul_left (numericRankThreshold m) (Nat.sub_le (leafK m h) 1)
    rwa [hfull] at hle
  have hlarge : 40000 * m ≤ h := by
    have hmul := Nat.mul_le_mul_left (10 * m) hb4000
    nlinarith [hmul, hrank']
  have hmargin : 20 * m + 5 ≤ h := by omega
  have hpoly : 2 * h + 20 * m * h + 3 ≤ 2 * h ^ 2 := by
    have hmul := Nat.mul_le_mul_right h hmargin
    nlinarith [hmul]
  have hblocks : h ^ 2 < blocks A h := by
    calc
      h ^ 2 = 1 * h ^ 2 := by simp
      _ ≤ A * h ^ 2 := Nat.mul_le_mul_right (h ^ 2) hA
      _ < blocks A h := numerator_lt_blocks A h
  refine ⟨hslarge, hsone, ?_⟩
  calc
    leafT m h + leafK m h + numericRankThreshold m * (leafK m h - 1) + 3 =
        2 * h + numericRankThreshold m * (leafK m h - 1) + 3 := by rw [leaf_split_total]
    _ ≤ 2 * h + 20 * m * h + 3 := by omega
    _ ≤ 2 * h ^ 2 := hpoly
    _ ≤ 2 * blocks A h := Nat.mul_le_mul_left 2 hblocks.le

theorem selected_numeric_tail_parameters
    (base : Nat → Nat) (cutoff : Real → Nat) {L m A : Nat} (hA : 1 ≤ A)
    (hsel : selector
      (fun j => max (analyticSourceHeightFloor (numericSourceBase base) cutoff j) (j + 2)) L =
        (m : WithBot Nat)) :
    20 * m ≤ leafK m (hBlock L m) ∧ 1 ≤ leafK m (hBlock L m) - 1 ∧
      leafT m (hBlock L m) + leafK m (hBlock L m) +
          numericRankThreshold m * (leafK m (hBlock L m) - 1) + 3 ≤
        2 * blocks A (hBlock L m) := by
  rcases selected_numeric_height base cutoff hsel with ⟨hm, hrank, _, _, hdiv⟩
  exact fixed_numeric_tail_parameters (by omega) hrank hdiv hA

theorem selected_numeric_real_parameters
    (base : Nat → Nat) (cutoff : Real → Nat) {L m : Nat}
    (hsel : selector
      (fun j => max (analyticSourceHeightFloor (numericSourceBase base) cutoff j) (j + 2)) L =
        (m : WithBot Nat)) :
    0 < actualSelectedRho m (hBlock L m) ∧
      actualSelectedRho m (hBlock L m) ≤ 1 / 4000 ∧
      (numericRankThreshold m : Real) * actualSelectedRho m (hBlock L m) = 10 * (m : Real) ∧
      (leafT m (hBlock L m) : Real) =
        2 * (1 - actualSelectedRho m (hBlock L m)) * (hBlock L m : Real) ∧
      (leafK m (hBlock L m) : Real) =
        2 * actualSelectedRho m (hBlock L m) * (hBlock L m : Real) := by
  rcases selected_spectral_parameters (numericSourceBase base) cutoff hsel with
    ⟨hm, _, _, _, _, _, hrhopos, hrho, hc, hs, _, _⟩
  have hmpos : 0 < m := by omega
  have hmsq : m ≤ m ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_left m hmpos
  have hb4000 : 4000 ≤ bOf m := by
    unfold bOf
    nlinarith [hmsq]
  have hbR : (0 : Real) < bOf m := by exact_mod_cast (show 0 < bOf m by omega)
  have hrhosmall : actualSelectedRho m (hBlock L m) ≤ 1 / 4000 := by
    rw [hrho]
    apply (div_le_div_iff₀ hbR (by norm_num : (0 : Real) < 4000)).2
    norm_num only [one_mul]
    exact_mod_cast hb4000
  have hrank : (numericRankThreshold m : Real) * actualSelectedRho m (hBlock L m) =
      10 * (m : Real) := by
    rw [hrho]
    unfold numericRankThreshold
    push_cast
    field_simp [ne_of_gt hbR] <;> ring
  exact ⟨hrhopos, hrhosmall, hrank, hc, hs⟩

end PvNP.RealizableHardness.ActualNumericSourceHeight
