import PvNP.RealizableHardness.ActualGlobalDensityBridge
import PvNP.RealizableHardness.ActualTaggedConcreteStarLaw

/-! The original complement law gives mass at least 4S to complements of
ordinary density at least 4S when the same-table side density is at least 8S. -/
namespace PvNP.RealizableHardness.ActualComplementDensityMass

open PvNP.RealizableHardness
open GrassmannCounting ActualFiniteLaw ActualChangedAmbient8SBoundary
open ActualSourceStarLaw ActualGlobalDensityBridge
open ActualTaggedComplementIncidence ActualTaggedComplementStarDensityBridge
open ActualTaggedConcreteStarLaw ActualTaggedOrderedSampleNonempty
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

theorem starDensity_nonneg_le_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {t d k : Nat} (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d) :
    0 ≤ StarDensity (k := k) hcenter hleaf C T ∧
      StarDensity (k := k) hcenter hleaf C T ≤ 1 := by
  haveI : Nonempty (Grass V t) := hcenter
  haveI : ∀ K : Grass V t, Nonempty (LeafOver K d) := hleaf
  have hkernel (K : Grass V t) (Ls : Fin k → LeafOver K d) :
      0 ≤ (uniformLaw (Grass V t)).mass K *
        (uniformLaw (Fin k → LeafOver K d)).mass Ls :=
    mul_nonneg (mass_nonneg _ K) (mass_nonneg _ Ls)
  have hnorm : (∑ K : Grass V t, ∑ Ls : Fin k → LeafOver K d,
      (uniformLaw (Grass V t)).mass K *
        (uniformLaw (Fin k → LeafOver K d)).mass Ls) = 1 := by
    calc
      _ = ∑ K : Grass V t, (uniformLaw (Grass V t)).mass K *
          (∑ Ls : Fin k → LeafOver K d,
            (uniformLaw (Fin k → LeafOver K d)).mass Ls) := by
        apply Finset.sum_congr rfl
        intro K _
        rw [Finset.mul_sum]
      _ = ∑ K : Grass V t, (uniformLaw (Grass V t)).mass K := by
        simp_rw [(uniformLaw (Fin k → LeafOver _ d)).normalized, mul_one]
      _ = 1 := (uniformLaw (Grass V t)).normalized
  constructor
  · unfold StarDensity
    apply Finset.sum_nonneg
    intro K _
    apply Finset.sum_nonneg
    intro Ls _
    exact mul_nonneg (hkernel K Ls) (by split_ifs <;> norm_num)
  · apply le_trans _ hnorm.le
    unfold StarDensity
    apply Finset.sum_le_sum
    intro K _
    apply Finset.sum_le_sum
    intro Ls _
    split_ifs <;> simp [hkernel K Ls]

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

theorem sideComplement_nonempty : Nonempty (SideComplement I copies U) := by
  obtain ⟨K⟩ := taggedCenterOver_nonempty I copies U (t := 0) (by omega)
  let Kside := centerToSide I copies U K
  have hover : 0 < Fintype.card (SideComplementOver I copies U Kside) := by
    rw [side_complements_over_card I copies U Kside]
    positivity
  obtain ⟨A⟩ := Fintype.card_pos_iff.mp hover
  exact ⟨A.1⟩

/-- The complete uniform complement law, independent of any success event. -/
def originalComplementLaw : FiniteLaw (SideComplement I copies U) := by
  haveI := sideComplement_nonempty I copies U
  exact uniformLaw (SideComplement I copies U)

theorem originalComplementLaw_mass (A : SideComplement I copies U) :
    (originalComplementLaw I copies U).mass A =
      (1 : Rat) / Fintype.card (SideComplement I copies U) := by
  unfold originalComplementLaw
  exact uniformLaw_apply _ _

theorem transportedStarDensity_nonneg_le_one {t h k : Nat}
    (A : SideComplement I copies U) (ht : t ≤ 2*h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies) :
    0 ≤ transportedStarDensity (t := t) (h := h) (k := k) I copies U A ht hh C T ∧
      transportedStarDensity (t := t) (h := h) (k := k) I copies U A ht hh C T ≤ 1 := by
  unfold transportedStarDensity
  exact starDensity_nonneg_le_one _ _ _ _

/-- The source-to-ordinary acceptance inclusion is averaged under the
unchanged actual complement marginal. -/
theorem sideDensity_le_original_complement_mean {t h k : Nat}
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies) :
    sideConditionalDensity I copies U t h k C T ≤
      ∑ A : SideComplement I copies U, (originalComplementLaw I copies U).mass A *
        transportedStarDensity (t := t) (h := h) (k := k) I copies U A ht hh C T := by
  have haverage : ordinaryComplementStarDensity I copies U t h k C T =
      ∑ A : SideComplement I copies U, (originalComplementLaw I copies U).mass A *
        complementFullAcceptMass (t := t) (h := h) (k := k) I copies U A C T := by
    simp_rw [originalComplementLaw_mass]
    unfold ordinaryComplementStarDensity complementFullAcceptMass
    apply Finset.sum_congr rfl
    intro A _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Ls _
    ring
  rw [sideConditionalDensity_eq_ordinaryComplementStarDensity I copies U ht hh C T,
    haverage]
  apply Finset.sum_le_sum
  intro A _
  exact mul_le_mul_of_nonneg_left
    (complementFullAcceptMass_le_transportedStarDensity
      (t := t) (h := h) (k := k) I copies U A ht hh C T)
    ((originalComplementLaw I copies U).nonneg A)

def goodComplementSet {t h k : Nat} (ht : t ≤ 2*h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies) (S : Rat) :
    Finset (SideComplement I copies U) :=
  Finset.univ.filter fun A => 4*S ≤
    transportedStarDensity (t := t) (h := h) (k := k) I copies U A ht hh C T

theorem mem_goodComplementSet_iff {t h k : Nat} (ht : t ≤ 2*h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies) (S : Rat)
    (A : SideComplement I copies U) :
    A ∈ goodComplementSet (k := k) I copies U ht hh C T S ↔ 4*S ≤
      transportedStarDensity (t := t) (h := h) (k := k) I copies U A ht hh C T := by
  simp only [goodComplementSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem original_good_complement_mass_lower {t h k : Nat}
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies)
    (S : Rat) (hS : 0 ≤ S)
    (hscore : 8*S ≤ sideConditionalDensity I copies U t h k C T) :
    4*S ≤ eventMass (originalComplementLaw I copies U)
      (goodComplementSet (k := k) I copies U ht hh C T S) := by
  let μ := originalComplementLaw I copies U
  let δ := fun A : SideComplement I copies U =>
    transportedStarDensity (t := t) (h := h) (k := k) I copies U A ht hh C T
  let G := goodComplementSet (k := k) I copies U ht hh C T S
  have hpoint (A : SideComplement I copies U) :
      μ.mass A * δ A ≤ μ.mass A * (4*S + if A ∈ G then 1 else 0) := by
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg A)
    by_cases hA : A ∈ G
    · rw [if_pos hA]
      have hδ := (transportedStarDensity_nonneg_le_one
        (k := k) I copies U A ht hh C T).2
      change δ A ≤ 1 at hδ
      linarith
    · rw [if_neg hA, add_zero]
      exact (lt_of_not_ge ((mem_goodComplementSet_iff
        (k := k) I copies U ht hh C T S A).not.mp hA)).le
  have hs := Finset.sum_le_sum fun A
    (_ : A ∈ (Finset.univ : Finset (SideComplement I copies U))) => hpoint A
  have hmean : 8*S ≤ ∑ A, μ.mass A * δ A :=
    hscore.trans (sideDensity_le_original_complement_mean (k := k) I copies U ht hh C T)
  have hevent : (∑ A, μ.mass A * (if A ∈ G then (1 : Rat) else 0)) =
      eventMass μ G := by
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter, eventMass]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    μ.normalized, one_mul, hevent] at hs
  change 4*S ≤ eventMass μ G
  linarith

end
end PvNP.RealizableHardness.ActualComplementDensityMass
