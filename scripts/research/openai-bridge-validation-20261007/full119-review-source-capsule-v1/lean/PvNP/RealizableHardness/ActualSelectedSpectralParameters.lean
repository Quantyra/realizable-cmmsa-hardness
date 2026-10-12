import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

/-! The selected CMMSA block size supplies genuine integral dimensions and
the caller's explicit analytic source-height cutoff at its actual spectral
parameter.  This module proves parameter compatibility only; it states no
spectral or moment estimate. -/

namespace PvNP.RealizableHardness.ActualSelectedSpectralParameters

open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

set_option autoImplicit false
noncomputable section

/-- Preserve the pre-existing source floor and add the source theorem's
actual rho-dependent height requirement. -/
def analyticSourceHeightFloor (base : Nat → Nat) (cutoff : Real → Nat) (m : Nat) : Nat :=
  max (base m) (cutoff (1 / (bOf m : Real)))

/-- The scalar source parameter is the ratio of the selected append width to
the full even leaf width. -/
def actualSelectedRho (m h : Nat) : Real :=
  (leafK m h : Real) / (2 * (h : Real))

theorem leafK_eq_two_mul_quotient {m h : Nat} (hdiv : bOf m ∣ h) :
    leafK m h = 2 * (h / bOf m) := by
  have hqle : h / bOf m ≤ h := Nat.div_le_self _ _
  have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
  unfold leafK leafT
  omega

theorem leaf_split_total {m h : Nat} : leafT m h + leafK m h = 2 * h := by
  have hTle : leafT m h ≤ 2 * h := by
    unfold leafT
    exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  unfold leafK leafT
  exact Nat.add_sub_of_le hTle

/-- Selector output gives all actual source guards and the exact split
`c+s=2h`, with rho identified from the selected dimensions and the true
source cutoff retained. -/
theorem selected_spectral_parameters
    (base : Nat → Nat) (cutoff : Real → Nat) {L m : Nat}
    (hsel : selector (fun j => max (analyticSourceHeightFloor base cutoff j) (j + 2)) L =
      (m : WithBot Nat)) :
    256 ≤ m ∧
    m + 2 ≤ hBlock L m ∧
    bOf m ∣ hBlock L m ∧
    0 < hBlock L m ∧
    0 < leafK m (hBlock L m) ∧
    leafT m (hBlock L m) + leafK m (hBlock L m) = 2 * hBlock L m ∧
    0 < actualSelectedRho m (hBlock L m) ∧
    actualSelectedRho m (hBlock L m) = 1 / (bOf m : Real) ∧
    (leafT m (hBlock L m) : Real) =
      2 * (1 - actualSelectedRho m (hBlock L m)) * (hBlock L m : Real) ∧
    (leafK m (hBlock L m) : Real) =
      2 * actualSelectedRho m (hBlock L m) * (hBlock L m : Real) ∧
    base m ≤ hBlock L m ∧
    cutoff (actualSelectedRho m (hBlock L m)) ≤ hBlock L m := by
  have hspec := selector_spec hsel
  rcases hspec.1 with ⟨hm, _, _, _, _, hdiv, _, hfloor, _⟩
  let h := hBlock L m
  have hh : m + 2 ≤ h := by
    exact (Nat.le_max_right (analyticSourceHeightFloor base cutoff m) (m + 2)).trans hfloor
  have hfloorCore : analyticSourceHeightFloor base cutoff m ≤ h :=
    (Nat.le_max_left (analyticSourceHeightFloor base cutoff m) (m + 2)).trans hfloor
  have hbaseFloor : base m ≤ analyticSourceHeightFloor base cutoff m :=
    Nat.le_max_left _ _
  have hcutFloor : cutoff (1 / (bOf m : Real)) ≤ analyticSourceHeightFloor base cutoff m :=
    Nat.le_max_right _ _
  have hbase : base m ≤ h := hbaseFloor.trans hfloorCore
  have hcutInv : cutoff (1 / (bOf m : Real)) ≤ h := hcutFloor.trans hfloorCore
  have hhpos : 0 < h := by omega
  have hbpos : 0 < bOf m := by
    dsimp [bOf]
    positivity
  have hqdecomp : bOf m * (h / bOf m) = h := by
    have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hmoddiv := Nat.mod_add_div h (bOf m)
    rw [hmod] at hmoddiv
    nlinarith [hmoddiv]
  have hqpos : 0 < h / bOf m := by
    by_contra hq
    have hq0 : h / bOf m = 0 := Nat.eq_zero_of_not_pos hq
    rw [hq0] at hqdecomp
    simp at hqdecomp
    omega
  have hsNat : leafK m h = 2 * (h / bOf m) := leafK_eq_two_mul_quotient hdiv
  have hsplit : leafT m h + leafK m h = 2 * h := leaf_split_total
  have hrho : actualSelectedRho m h = 1 / (bOf m : Real) := by
    rw [actualSelectedRho, hsNat]
    have hqcast : (bOf m : Real) * ((h / bOf m : Nat) : Real) = (h : Real) := by
      exact_mod_cast hqdecomp
    have hbR : (bOf m : Real) ≠ 0 := by positivity
    have hR : (h : Real) ≠ 0 := by positivity
    push_cast
    field_simp [hbR, hR]
    rw [← hqcast]
    ring
  have hrhopos : 0 < actualSelectedRho m h := by rw [hrho]; positivity
  have hsReal : (leafK m h : Real) = 2 * actualSelectedRho m h * (h : Real) := by
    unfold actualSelectedRho
    have hhR : (2 : Real) * (h : Real) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hcReal : (leafT m h : Real) =
      2 * (1 - actualSelectedRho m h) * (h : Real) := by
    have hsplitR : (leafT m h : Real) + (leafK m h : Real) = 2 * (h : Real) := by
      exact_mod_cast hsplit
    rw [hsReal] at hsplitR
    nlinarith
  refine ⟨hm, hh, hdiv, hhpos, ?_, hsplit, hrhopos, hrho, hcReal, hsReal, hbase, ?_⟩
  · rw [hsNat]
    positivity
  · rw [hrho]
    exact hcutInv

/-- The selector floor constructor used by source-theorem callers. -/
def selectedAnalyticFloor (base : Nat → Nat) (cutoff : Real → Nat) (m : Nat) : Nat :=
  max (analyticSourceHeightFloor base cutoff m) (m + 2)

end
end PvNP.RealizableHardness.ActualSelectedSpectralParameters
