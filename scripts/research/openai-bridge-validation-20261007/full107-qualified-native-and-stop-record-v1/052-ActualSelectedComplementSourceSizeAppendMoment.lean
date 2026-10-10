import PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.SamplerParameters

/-! A selected actual side complement, in its common coordinate carrier, has
the same center mass and a genuine appended-matrix moment bound. -/
namespace PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAppendMoment

open ActualOccurrenceAllocation
open ActualTaggedComplementIncidence
open ActualTaggedConcreteStarLaw
open ActualTaggedFixedTableAcceptance
open ActualOrdinaryStarWeightedSelection
open ActualFixedFunctionalStarMoment
open ActualTaggedComplementStarDensityBridge
open ActualFixedFunctionalBinaryMatrixMoment
open ActualComplementCoordinateMassBridge
open ActualFixedFunctionalAppendOperator
open ActualStarFixedRhoDimensionGuard
open ActualCmmsaAdmissibilitySelector
open ActualCmmsaParameterReconciliation
open SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem selected_rankloss_exponent
    {m h J c s A : Nat} (hm : 256 ≤ m) (hh : m + 2 ≤ h)
    (hA : 1 ≤ A) (hJ : J = blocks A h)
    (hc : c = leafT m h) (hs : s = leafK m h) :
    c + s = 2 * h ∧ c + m * s + 2 * h ≤ 2 * J := by
  subst hJ
  subst hc
  subst hs
  have hmpos : 0 < m := by omega
  have htle : leafT m h ≤ 2 * h := by
    dsimp [leafT]
    exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  have hsle : leafK m h ≤ 2 * h := by
    dsimp [leafK]
    exact Nat.sub_le _ _
  have hsum : leafT m h + leafK m h = 2 * h := by
    change leafT m h + (2 * h - leafT m h) = 2 * h
    exact Nat.add_sub_of_le htle
  have hpoly : leafT m h + m * leafK m h + 2 * h ≤ 2 * h ^ 2 := by
    have hmul : m + 1 ≤ h - 1 := by omega
    calc
      leafT m h + m * leafK m h + 2 * h ≤ 2 * h + m * (2 * h) + 2 * h := by
        exact Nat.add_le_add (Nat.add_le_add htle (Nat.mul_le_mul_left m hsle)) le_rfl
      _ = 2 * h * (m + 1) + 2 * h := by ring
      _ ≤ 2 * h * (h - 1) + 2 * h := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (2 * h) hmul) _
      _ = 2 * h ^ 2 := by
        have hminus : h - 1 + 1 = h := Nat.sub_add_cancel (by omega)
        calc
          2 * h * (h - 1) + 2 * h = 2 * h * ((h - 1) + 1) := by ring
          _ = 2 * h * h := by rw [hminus]
          _ = 2 * h ^ 2 := by ring
  have hpow : h ^ 2 < blocks A h := by
    calc
      h ^ 2 = 1 * h ^ 2 := by simp
      _ ≤ A * h ^ 2 := Nat.mul_le_mul_right (h ^ 2) hA
      _ < blocks A h := by
        simpa only [one_mul] using numerator_lt_blocks A h
  constructor
  · exact hsum
  · have hsmall : leafT m h + m * leafK m h + 2 * h ≤ 2 * h ^ 2 := hpoly
    have hb : 2 * h ^ 2 ≤ 2 * blocks A h := Nat.mul_le_mul_left 2 hpow.le
    simpa using hsmall.trans hb

private theorem rankloss_from_exponent
    {h J c s m : Nat} (hh : 0 < h)
    (hsum : c + s = 2 * h)
    (hbudget : c + m * s + 2 * h ≤ 2 * J) :
    ((c + m * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
        (2 : Real) ^ (2 * J) ≤ 1 / 2 := by
  let N0 := c + m * s
  have hNpos : 0 < 2 * h := by omega
  have hnumerator : (N0 : Real) ≤ (2 : Real) ^ N0 := by
    have hn : N0 < 2 ^ N0 := Nat.lt_two_pow_self
    exact_mod_cast hn.le
  have hexp : N0 + (2 * h - 1) ≤ 2 * J - 1 := by omega
  have hp : (2 : Real) ^ (N0 + (2 * h - 1)) ≤
      (2 : Real) ^ (2 * J - 1) := by
    exact pow_le_pow_right₀ (by norm_num) hexp
  have hprod : (N0 : Real) * (2 : Real) ^ (2 * h - 1) ≤
      (2 : Real) ^ (2 * J - 1) := by
    calc
      (N0 : Real) * (2 : Real) ^ (2 * h - 1) ≤
          (2 : Real) ^ N0 * (2 : Real) ^ (2 * h - 1) :=
        mul_le_mul_of_nonneg_right hnumerator (by positivity)
      _ = (2 : Real) ^ (N0 + (2 * h - 1)) := by rw [← pow_add]
      _ ≤ (2 : Real) ^ (2 * J - 1) := hp
  rw [hsum]
  exact (div_le_iff₀ (by positivity : (0 : Real) < (2 : Real) ^ (2 * J))).2
    (calc
      (N0 : Real) * (2 : Real) ^ (2 * h - 1) ≤ (2 : Real) ^ (2 * J - 1) := hprod
      _ = (1 / 2 : Real) * (2 : Real) ^ (2 * J) := by
        have he : 2 * J - 1 + 1 = 2 * J := by omega
        have hden : (2 : Real) ^ (2 * J) =
            (2 : Real) ^ (2 * J - 1) * 2 := by
          calc
            (2 : Real) ^ (2 * J) = (2 : Real) ^ ((2 * J - 1) + 1) :=
              congrArg (fun e : Nat => (2 : Real) ^ e) he.symm
            _ = (2 : Real) ^ (2 * J - 1) * 2 := by rw [pow_succ]
        rw [hden]
        ring)

theorem selected_actual_append_moment
    {N rows m L samplerA : Nat} (I : Instance N rows) (copies : Nat)
    (U : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (A : SideComplement I copies U)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1)
    (sourceHMin : Nat → Nat)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (m : WithBot Nat))
    (hA : 1 ≤ samplerA) :
    let h := hBlock L m
    let J := blocks samplerA h
    let c := leafT m h
    let s := leafK m h
    let k := m
    let n := 2 * J
    (matchingStarMass (V := A.1) (m := k) (Nat.le_add_right c s)
      (by
        have hs := selector_spec hsel
        rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
        have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
        have hp : h ^ 2 < J := by
          dsimp [h, J]
          simpa only [one_mul] using
            ((Nat.mul_le_mul_right (hBlock L m ^ 2) hA).trans_lt
              (numerator_lt_blocks samplerA (hBlock L m)))
        have hpos : 0 < h := by omega
        have hle : h ≤ h ^ 2 := by
          simpa [pow_two] using (Nat.le_mul_of_pos_left h hpos)
        rw [sideComplement_finrank I copies U A]
        have hd := selected_rankloss_exponent hm hh hA rfl rfl rfl
        have _hsum := hd.1
        have _hbudget := hd.2
        change c + s ≤ 2 * J
        omega)
      (transportedCenterTable I copies U A C)
      (transportedLeafTable I copies U A T) f : Real) ≤
        2 * actualAppendRankImageMoment (n := n) (c := c) (s := s)
          (fun R => centerMatchBit (selectedCoordinateCenterTable I copies U A C)
            (coordinateFunctional I copies U A f) R)
          (fun W => leafMatchBit (selectedCoordinateLeafTable I copies U A T)
            (coordinateFunctional I copies U A f) W) k := by
  intro h J c s k n
  have hs := selector_spec hsel
  rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
  have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
  have hbudgetData := selected_rankloss_exponent hm hh hA rfl rfl rfl
  have hp : h ^ 2 < J := by
    dsimp [h, J]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right (hBlock L m ^ 2) hA).trans_lt
        (numerator_lt_blocks samplerA (hBlock L m)))
  have hpos : 0 < h := by omega
  have hle : h ≤ h ^ 2 := by
    simpa [pow_two] using (Nat.le_mul_of_pos_left h hpos)
  have hdim : c + s ≤ Module.finrank (ZMod 2) A.1 := by
    rw [sideComplement_finrank I copies U A]
    have hsum := hbudgetData.1
    have hbudget := hbudgetData.2
    change c + s ≤ 2 * J
    omega
  have hsum : c + s = 2 * h := hbudgetData.1
  have hD : 0 < c + s := by rw [hsum]; omega
  have hbudget : c + m * s + 2 * h ≤ 2 * J := hbudgetData.2
  have hsmall := rankloss_from_exponent hpos
    hbudgetData.1 hbudget
  have hfinrank : Module.finrank (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) = 2 * J := by
    simp [ActualFixedFunctionalAppendOperator.CoordinateAmbient, n]
  have hsmall' : ((c + k * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
      (2 : Real) ^ Module.finrank (ZMod 2)
        (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) ≤ 1 / 2 := by
    rw [hfinrank]
    simpa [c, s, k] using hsmall
  have hbound := matchingStarMass_cast_le_twice_actualAppendRankImageMoment
    (n := n) (c := c) (s := s) (k := k)
    (by
      simp [ActualFixedFunctionalAppendOperator.CoordinateAmbient, n]
      have hd := selected_rankloss_exponent hm hh hA rfl rfl rfl
      have hsum' := hd.1
      have hbudget' := hd.2
      change leafT m h + leafK m h ≤ 2 * J
      omega) hD hsmall'
    (selectedCoordinateCenterTable I copies U A C)
    (selectedCoordinateLeafTable I copies U A T)
    (coordinateFunctional I copies U A f)
  have hcoord := matchingStarMass_actual_coordinate (m := k) I copies U A
    (Nat.le_add_right c s) hdim C T f
  calc
    (matchingStarMass (V := A.1) (m := k) (Nat.le_add_right c s)
      hdim
      (transportedCenterTable I copies U A C)
      (transportedLeafTable I copies U A T) f : Real) =
        (matchingStarMass (V := CoordAmbient J) (m := k)
          (Nat.le_add_right c s)
          (actualCoordinateDimensionBound I copies U A hdim)
          (selectedCoordinateCenterTable I copies U A C)
          (selectedCoordinateLeafTable I copies U A T)
          (coordinateFunctional I copies U A f) : Real) := by
            exact_mod_cast hcoord
    _ ≤ _ := hbound

theorem selected_actual_center_identity
    {N rows m L samplerA : Nat} (I : Instance N rows) (copies : Nat)
    (U : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (A : SideComplement I copies U)
    (C : TaggedCenterTable I copies)
    (f : Module.Dual (ZMod 2) A.1)
    (sourceHMin : Nat → Nat)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (m : WithBot Nat))
    (hA : 1 ≤ samplerA) :
    let h := hBlock L m
    let J := blocks samplerA h
    let c := leafT m h
    let s := leafK m h
    let k := m
    (matchingCenterMass (V := A.1) (m := k) (Nat.le_add_right c s)
      (by
        have hs := selector_spec hsel
        rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
        have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
        have hp : h ^ 2 < J := by
          dsimp [h, J]
          simpa only [one_mul] using
            ((Nat.mul_le_mul_right (hBlock L m ^ 2) hA).trans_lt
              (numerator_lt_blocks samplerA (hBlock L m)))
        have hpos : 0 < h := by omega
        have hle : h ≤ h ^ 2 := by
          simpa [pow_two] using (Nat.le_mul_of_pos_left h hpos)
        rw [sideComplement_finrank I copies U A]
        have hd := selected_rankloss_exponent hm hh hA rfl rfl rfl
        have _hsum := hd.1
        have _hbudget := hd.2
        change c + s ≤ 2 * J
        omega)
      (transportedCenterTable I copies U A C) f) =
        matchingCenterMass (V := CoordAmbient J) (m := k)
          (Nat.le_add_right c s)
          (by
            have hs := selector_spec hsel
            rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
            have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
            have hd := selected_rankloss_exponent hm hh hA rfl rfl rfl
            simp [CoordAmbient]
            omega)
          (selectedCoordinateCenterTable I copies U A C)
          (coordinateFunctional I copies U A f) := by
  intro h J c s k
  have hs := selector_spec hsel
  rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
  have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
  have hp : h ^ 2 < J := by
    dsimp [h, J]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right (hBlock L m ^ 2) hA).trans_lt
        (numerator_lt_blocks samplerA (hBlock L m)))
  have hpos : 0 < h := by omega
  have hle : h ≤ h ^ 2 := by
    simpa [pow_two] using (Nat.le_mul_of_pos_left h hpos)
  have hdim : c + s ≤ Module.finrank (ZMod 2) A.1 := by
    rw [sideComplement_finrank I copies U A]
    have hd := selected_rankloss_exponent hm hh hA rfl rfl rfl
    have hsum := hd.1
    have hbudget := hd.2
    change c + s ≤ 2 * J
    omega
  have hcoord := matchingCenterMass_actual_coordinate (m := k) I copies U A
    (Nat.le_add_right c s) hdim C f
  exact hcoord

end
end PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAppendMoment
