import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.SamplerParameters

/-! Exact fixed-rho source-star dimension arithmetic. This module proves the
numeric guard and its selector-facing cutoff specialization; actual source
soundness and draw-law transport remain separate.
-/

namespace PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw

def leafT (m h : Nat) : Nat := 2 * (h - h / bOf m)
def leafK (m h : Nat) : Nat := 2 * h - leafT m h
def badExponent (m h : Nat) : Nat := 2 * m * (h - 1000 * (h / bOf m))

/-- With the fixed-rho quotient `q=h/(4000m²)`, the ambient exponent budget
fits the actual sampler block count. The hypotheses retain the genuine
pointwise height cutoff and positive sampler exponent. -/
theorem fixedRho_ambient_dimension_guard
    {m A h : Nat} (hm : 256 ≤ m) (hh : m + 2 ≤ h)
    (hdiv : bOf m ∣ h) (hA : 1 ≤ A) :
    leafT m h + m * leafK m h + badExponent m h + 2 ≤
      2 * blocks A h := by
  let q := h / bOf m
  let b := bOf m
  have hmpos : 0 < m := by omega
  have hmsq : m ≤ m ^ 2 := by
    simpa [pow_two] using (Nat.le_mul_of_pos_left m hmpos)
  have hbpos : 0 < b := by
    dsimp [b, bOf]
    positivity
  have hb1000 : 1000 ≤ b := by
    dsimp [b, bOf]
    nlinarith [hmsq]
  have hb3m : 3 * m ≤ b := by
    dsimp [b, bOf]
    calc
      3 * m ≤ 4000 * m := Nat.mul_le_mul_right m (by decide)
      _ ≤ 4000 * m ^ 2 := Nat.mul_le_mul_left 4000 hmsq
  have hmod : h % b = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hdecomp : b * q = h := by
    dsimp [q]
    have hmoddiv := Nat.mod_add_div h b
    rw [hmod] at hmoddiv
    simpa using hmoddiv
  have hqpos : 0 < q := by
    by_contra hq
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    rw [hq0] at hdecomp
    simp at hdecomp
    omega
  have hqle : q ≤ h := by
    calc
      q ≤ b * q := Nat.le_mul_of_pos_left q hbpos
      _ = h := hdecomp
  have h1000q : 1000 * q ≤ h := by
    calc
      1000 * q ≤ b * q := Nat.mul_le_mul_right q hb1000
      _ = h := hdecomp
  have h2m3 : 2 * m + 3 ≤ h := by
    have hbq : b ≤ b * q := by
      calc
        b ≤ q * b := Nat.le_mul_of_pos_left b hqpos
        _ = b * q := Nat.mul_comm _ _
    have hbig : 3 * m ≤ h := hb3m.trans (by rw [← hdecomp]; exact hbq)
    omega
  have hinc : leafK m h = 2 * q := by
    dsimp [leafK, leafT, q]
    have hsub : h - h / b + h / b = h := Nat.sub_add_cancel hqle
    omega
  have hmkE : m * leafK m h + badExponent m h ≤ 2 * m * h := by
    rw [hinc]
    have hq1000 : q ≤ 1000 * q :=
      Nat.le_mul_of_pos_left q (by decide : 0 < 1000)
    calc
      m * (2 * q) + 2 * m * (h - 1000 * q) =
          2 * m * q + 2 * m * (h - 1000 * q) := by ring
      _ ≤ 2 * m * (1000 * q) + 2 * m * (h - 1000 * q) := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left (2 * m) hq1000) _
      _ = 2 * m * h := by
          calc
            2 * m * (1000 * q) + 2 * m * (h - 1000 * q) =
                2 * m * (1000 * q + (h - 1000 * q)) := by ring
            _ = 2 * m * ((h - 1000 * q) + 1000 * q) := by rw [Nat.add_comm]
            _ = 2 * m * h := by rw [Nat.sub_add_cancel h1000q]
  have ht : leafT m h ≤ 2 * h := by
    dsimp [leafT]
    exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  have hsmall : leafT m h + m * leafK m h + badExponent m h + 2 ≤
      2 * h + 2 * m * h + 2 := by
    calc
      leafT m h + m * leafK m h + badExponent m h + 2 =
          (leafT m h + (m * leafK m h + badExponent m h)) + 2 := by omega
      _ ≤ (2 * h + 2 * m * h) + 2 := by
          exact Nat.add_le_add_right (Nat.add_le_add ht hmkE) 2
      _ = 2 * h + 2 * m * h + 2 := by omega
  have hpoly : 2 * h + 2 * m * h + 2 ≤ 2 * h ^ 2 := by
    have hmul : (2 * m + 3) * h ≤ h * h := Nat.mul_le_mul_right h h2m3
    nlinarith [hmul]
  have hblocks : h ^ 2 < blocks A h := by
    calc
      h ^ 2 = 1 * h ^ 2 := by simp
      _ ≤ A * h ^ 2 := Nat.mul_le_mul_right (h ^ 2) hA
      _ < blocks A h := numerator_lt_blocks A h
  have hblocks2 : 2 * h ^ 2 ≤ 2 * blocks A h :=
    Nat.mul_le_mul_left 2 hblocks.le
  exact hsmall.trans (hpoly.trans hblocks2)

/-- The same guard in the already-centered quotient dimension `2J−t`.
This is the form to compare with a quotient-carried scalar estimate; it does
not subtract the original center dimension a second time. -/
theorem fixedRho_quotient_dimension_guard
    {m A h : Nat} (hm : 256 ≤ m) (hh : m + 2 ≤ h)
    (hdiv : bOf m ∣ h) (hA : 1 ≤ A) :
    m * leafK m h + badExponent m h + 2 ≤
      2 * blocks A h - leafT m h := by
  apply Nat.le_sub_of_add_le
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    fixedRho_ambient_dimension_guard hm hh hdiv hA

/-- Selector-facing specialization. The new pointwise height cutoff is
combined by `max` with the pre-existing source cutoff, so no prior selector
condition is dropped. `A` remains an explicit positive caller-supplied
sampler parameter; this theorem does not discharge source soundness. -/
theorem selected_fixedRho_quotient_dimension_guard
    (sourceHMin : Nat → Nat) {L m A : Nat} (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (m : WithBot Nat)) :
    m * leafK m (hBlock L m) + badExponent m (hBlock L m) + 2 ≤
      2 * blocks A (hBlock L m) - leafT m (hBlock L m) := by
  have hspec := selector_spec hsel
  rcases hspec.1 with ⟨hm, _, _, _, _, hdiv, _, hcut, _⟩
  have hh : m + 2 ≤ hBlock L m := by
    exact (Nat.le_max_right (sourceHMin m) (m + 2)).trans hcut
  exact fixedRho_quotient_dimension_guard hm hh hdiv hA

/-- The selected scalar guard expressed at the actual `CenterQuotient`
carrier. For the source-law application, the scalar ambient is
`questionCoordinateSpace center`, the fixed subspace is
`centerSpanInCoordinate center` of rank `J + leafT`, and each leaf has rank
`J + 2*h`. Their quotient is `CenterQuotient center`, of dimension
`2*J - leafT`, with quotient increment rank `2*h - leafT`. This theorem proves
only the numeric guard; law and event transport remain separate. -/
theorem selected_actual_center_quotient_dimension_guard
    {N m L A : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (center : QuestionCenter I (blocks A (hBlock L m)) (leafT m (hBlock L m)))
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (m : WithBot Nat)) :
    m * leafK m (hBlock L m) + badExponent m (hBlock L m) + 2 ≤
      Module.finrank (ZMod 2) (CenterQuotient center) := by
  rw [centerQuotient_finrank center]
  exact selected_fixedRho_quotient_dimension_guard sourceHMin hA hsel

end PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
