import PvNP.RealizableHardness.ActualCliqueJointLaw

namespace PvNP.RealizableHardness.ActualCliqueCollisionTransfer

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

local instance scoreLeafCliqueFintype {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    Fintype (LeafClique I J h) :=
  Fintype.ofInjective (fun C : LeafClique I J h => C.1) Subtype.val_injective

local instance scoreCliqueRepresentativeFintype {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m} (C : LeafClique I J h) :
    Fintype (CliqueRepresentative C) :=
  Fintype.ofInjective (fun v : CliqueRepresentative C => v.1) Subtype.val_injective

private theorem uniformMean_sub {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℚ) :
    uniformMean α (fun x => f x - g x) =
      uniformMean α f - uniformMean α g := by
  unfold uniformMean
  rw [Finset.sum_sub_distrib]
  ring

private theorem uniformMean_swap
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → β → ℚ) :
    uniformMean α (fun a => uniformMean β (f a)) =
      uniformMean β (fun b => uniformMean α (fun a => f a b)) := by
  have hα : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformMean
  rw [Finset.sum_div, Finset.sum_div]
  field_simp [hα, hβ]
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [Finset.sum_comm]

private theorem uniformMean_indicator_nonneg
    {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    0 ≤ uniformMean α (fun x => if p x then 1 else 0) := by
  unfold uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg (fun x hx => by
      by_cases hp : p x
      · rw [if_pos hp] <;> norm_num
      · rw [if_neg hp] <;> norm_num)
  · exact_mod_cast (Nat.zero_le (Fintype.card α))

private theorem uniformMean_indicator_le_one
    {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformMean α (fun x => if p x then 1 else 0) ≤ 1 := by
  unfold uniformMean
  have hsum :
      (∑ x : α, (if p x then (1 : ℚ) else 0)) ≤
        ∑ x : α, (1 : ℚ) := by
    exact Finset.sum_le_sum (fun x hx => by
      by_cases hp : p x
      · rw [if_pos hp] <;> norm_num
      · rw [if_neg hp] <;> norm_num)
  have hcard : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardpos : (0 : ℚ) ≤ Fintype.card α := by positivity
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hsum' :
      (∑ x : α, (if p x then (1 : ℚ) else 0)) ≤
        (Fintype.card α : ℚ) := by
    simpa only [Finset.card_univ, mul_one] using hsum
  calc
    (∑ x : α, (if p x then (1 : ℚ) else 0)) / Fintype.card α ≤
        (Fintype.card α : ℚ) / Fintype.card α :=
      div_le_div_of_nonneg_right hsum' hcardpos
    _ = 1 := div_self hcard

private theorem exists_le_uniformMean
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ℚ) :
    ∃ x : α, uniformMean α f ≤ f x := by
  have hcard : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum :
      (∑ x : α, uniformMean α f) ≤ ∑ x : α, f x := by
    have heq : (∑ x : α, uniformMean α f) = ∑ x : α, f x := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      unfold uniformMean
      exact mul_div_cancel₀ _ hcard
    exact heq.le
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨x, hx⟩

noncomputable def originalScore
    {N m J h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : LeafTable I J h)
    (vs : Ω → Fin k → LeafVertex I J h)
    (accept : (ω : Ω) → LabelTuple (vs ω) → Prop) : ℚ :=
  uniformMean Ω (fun ω =>
    uniformMean (IndependentChoice (vs ω)) (fun r =>
      if accept ω (independentLabels T (vs ω) r) then 1 else 0))

noncomputable def selectedScore
    {N m J h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (vs : Ω → Fin k → LeafVertex I J h)
    (accept : (ω : Ω) → LabelTuple (vs ω) → Prop) : ℚ :=
  uniformMean Ω (fun ω =>
    if accept ω (selectedLabels T s (vs ω)) then 1 else 0)

noncomputable def collisionMass
    {N m J h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (vs : Ω → Fin k → LeafVertex I J h) : ℚ :=
  uniformMean Ω (fun ω => if CliqueCollision (vs ω) then 1 else 0)

theorem exists_selectedTable_score_ge_sub_collision
    {N m J h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : LeafTable I J h)
    (vs : Ω → Fin k → LeafVertex I J h)
    (accept : (ω : Ω) → LabelTuple (vs ω) → Prop) :
  ∃ s : RepresentativeChoice I J h,
    originalScore T vs accept - collisionMass vs ≤
      selectedScore T s vs accept := by
  have hpoint (ω : Ω) :
      uniformMean (IndependentChoice (vs ω)) (fun r =>
          if accept ω (independentLabels T (vs ω) r) then 1 else 0) -
          (if CliqueCollision (vs ω) then 1 else 0) ≤
        uniformMean (RepresentativeChoice I J h) (fun s =>
          if accept ω (selectedLabels T s (vs ω)) then 1 else 0) := by
    by_cases hdist : DistinctCliques (vs ω)
    · have hLaw := jointLaw_eq_of_distinctCliques T (vs ω) hdist
          (fun xs => if accept ω xs then 1 else 0)
      rw [show (if CliqueCollision (vs ω) then (1 : ℚ) else 0) = 0 by
        simp [CliqueCollision, hdist], sub_zero]
      exact hLaw.ge
    · have hA := uniformMean_indicator_le_one
          (fun r : IndependentChoice (vs ω) =>
            accept ω (independentLabels T (vs ω) r))
      have hB := uniformMean_indicator_nonneg
          (fun s : RepresentativeChoice I J h =>
            accept ω (selectedLabels T s (vs ω)))
      rw [show (if CliqueCollision (vs ω) then (1 : ℚ) else 0) = 1 by
        simp [CliqueCollision, hdist]]
      exact (sub_nonpos.mpr hA).trans hB
  have havg :
      uniformMean Ω (fun ω =>
        (uniformMean (IndependentChoice (vs ω)) (fun r =>
          if accept ω (independentLabels T (vs ω) r) then 1 else 0)) -
          (if CliqueCollision (vs ω) then 1 else 0)) ≤
        uniformMean Ω (fun ω =>
          uniformMean (RepresentativeChoice I J h) (fun s =>
            if accept ω (selectedLabels T s (vs ω)) then 1 else 0)) := by
    unfold uniformMean
    apply div_le_div_of_nonneg_right
    · exact Finset.sum_le_sum (fun ω hω => hpoint ω)
    · exact Nat.cast_nonneg _
  have hscore :
      originalScore T vs accept - collisionMass vs ≤
        uniformMean Ω (fun ω =>
          uniformMean (RepresentativeChoice I J h) (fun s =>
            if accept ω (selectedLabels T s (vs ω)) then 1 else 0)) := by
    change
      uniformMean Ω (fun ω =>
          uniformMean (IndependentChoice (vs ω)) (fun r =>
            if accept ω (independentLabels T (vs ω) r) then 1 else 0)) -
        uniformMean Ω (fun ω => if CliqueCollision (vs ω) then 1 else 0) ≤ _
    rw [← uniformMean_sub]
    exact havg
  have hswap :
      uniformMean Ω (fun ω =>
          uniformMean (RepresentativeChoice I J h) (fun s =>
            if accept ω (selectedLabels T s (vs ω)) then 1 else 0)) =
        uniformMean (RepresentativeChoice I J h) (fun s =>
          uniformMean Ω (fun ω =>
            if accept ω (selectedLabels T s (vs ω)) then 1 else 0)) := by
    exact uniformMean_swap (fun ω s =>
      if accept ω (selectedLabels T s (vs ω)) then 1 else 0)
  obtain ⟨s, hs⟩ := exists_le_uniformMean
    (fun s : RepresentativeChoice I J h => selectedScore T s vs accept)
  refine ⟨s, ?_⟩
  calc
    originalScore T vs accept - collisionMass vs ≤
        uniformMean Ω (fun ω =>
          uniformMean (RepresentativeChoice I J h) (fun s =>
            if accept ω (selectedLabels T s (vs ω)) then 1 else 0)) := hscore
    _ = uniformMean (RepresentativeChoice I J h) (fun s =>
          selectedScore T s vs accept) := by
      rw [hswap]
      rfl
    _ ≤ selectedScore T s vs accept := hs

end
end PvNP.RealizableHardness.ActualCliqueCollisionTransfer
