import PvNP.RealizableHardness.ActualSourceStarCompleteness
import PvNP.RealizableHardness.ActualTaggedFailureTransport
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualQuestionMassBridge
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

local instance sourceStarSoundnessRowIdDecidableEq : DecidableEq I.RowId :=
  Classical.decEq _

local instance sourceStarSoundnessGlobalVarDecidableEq : DecidableEq I.GlobalVar :=
  inferInstance

local instance sourceStarSoundnessRowIdFintype : Fintype I.RowId :=
  inferInstance

/-- `1` if some queried equation is violated by `x`, else `0`.
The next consumer applies certified `actualTaggedGoodFailureMean_sourceExtension_le`
to `presentedEnum`; this module does not re-prove that tagged mean. -/
noncomputable def questionFailIndicator
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) : ℝ :=
  if ∃ e ∈ P.U, (Finite3LinSource.ofActual I).badRow x e = true then 1 else 0

theorem questionFailIndicator_nonneg
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    0 ≤ questionFailIndicator P x := by
  unfold questionFailIndicator
  split <;> norm_num

theorem questionFailIndicator_le_one
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    questionFailIndicator P x ≤ 1 := by
  unfold questionFailIndicator
  split <;> norm_num

private theorem questionFailIndicator_eq_zero_or_one
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    questionFailIndicator P x = 0 ∨ questionFailIndicator P x = 1 := by
  unfold questionFailIndicator
  split <;> simp

theorem questionFailIndicator_eq_zero_iff
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    questionFailIndicator P x = 0 ↔
      RespectsAt P rfl (honestRawLabel (D := P.domain) x) := by
  unfold questionFailIndicator
  constructor
  · intro hzero
    apply (honestRawLabel_respects_iff P x).mpr
    intro e he
    by_cases hb : (Finite3LinSource.ofActual I).badRow x e = true
    · have hex :
          ∃ e ∈ P.U, (Finite3LinSource.ofActual I).badRow x e = true :=
        ⟨e, he, hb⟩
      simp [hex] at hzero
    · exact Bool.eq_false_iff.mpr hb
  · intro hresp
    have hfalse := (honestRawLabel_respects_iff P x).mp hresp
    split
    · rename_i hex
      obtain ⟨e, he, hb⟩ := hex
      have := hfalse e he
      rw [this] at hb
      exact (Bool.false_ne_true hb).elim
    · rfl

theorem questionFailIndicator_eq_one_iff
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    questionFailIndicator P x = 1 ↔
      ¬ RespectsAt P rfl (honestRawLabel (D := P.domain) x) := by
  constructor
  · intro h1 hresp
    have h0 := (questionFailIndicator_eq_zero_iff P x).mpr hresp
    rw [h0] at h1
    exact zero_ne_one h1
  · intro hnot
    cases questionFailIndicator_eq_zero_or_one P x with
    | inl h0 =>
      exact (hnot ((questionFailIndicator_eq_zero_iff P x).mp h0)).elim
    | inr h1 =>
      exact h1

/-- Enumerate `P.U` in `Fin J` using `P.card_U`. -/
noncomputable def presentedEnum (P : PresentedLeaf I J h) : Fin J → I.RowId :=
  fun i => ((P.U.equivFin.symm) (i.cast P.card_U.symm)).1

theorem presentedEnum_mem (P : PresentedLeaf I J h) (i : Fin J) :
    presentedEnum P i ∈ P.U :=
  ((P.U.equivFin.symm) (i.cast P.card_U.symm)).2

theorem presentedEnum_surj (P : PresentedLeaf I J h)
    (e : I.RowId) (he : e ∈ P.U) : ∃ i : Fin J, presentedEnum P i = e := by
  refine ⟨(P.U.equivFin ⟨e, he⟩).cast P.card_U, ?_⟩
  change ((P.U.equivFin.symm)
      (((P.U.equivFin ⟨e, he⟩).cast P.card_U).cast P.card_U.symm)).1 = e
  have hcast :
      ((P.U.equivFin ⟨e, he⟩).cast P.card_U).cast P.card_U.symm =
        P.U.equivFin ⟨e, he⟩ := by
    ext
    simp
  rw [hcast, Equiv.symm_apply_apply]

theorem questionFailIndicator_eq_baseFailure
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    questionFailIndicator P x =
      actualBaseFailureIndicator I x (presentedEnum P) := by
  unfold questionFailIndicator actualBaseFailureIndicator
  have hiff :
      (∃ e ∈ P.U, (Finite3LinSource.ofActual I).badRow x e = true) ↔
        (∃ j : Fin J, (Finite3LinSource.ofActual I).badRow x (presentedEnum P j) =
          true) := by
    constructor
    · rintro ⟨e, he, hb⟩
      obtain ⟨j, hj⟩ := presentedEnum_surj P e he
      refine ⟨j, ?_⟩
      rwa [hj]
    · rintro ⟨j, hj⟩
      exact ⟨presentedEnum P j, presentedEnum_mem P j, hj⟩
  by_cases hp : ∃ e ∈ P.U, (Finite3LinSource.ofActual I).badRow x e = true
  · have hq := hiff.mp hp
    simp [hp, hq]
  · have hq := hiff.not.mp hp
    simp [hp, hq]

private theorem questionFailTerm_nonneg
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) (e : I.RowId) :
    0 ≤ (if e ∈ P.U ∧ (Finite3LinSource.ofActual I).badRow x e = true
      then (1 : ℝ) else 0) := by
  by_cases h : e ∈ P.U ∧ (Finite3LinSource.ofActual I).badRow x e = true
  · simp [h]
  · simp [h]

theorem questionFailIndicator_le_sum
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    questionFailIndicator P x ≤
      ∑ e : I.RowId, if e ∈ P.U ∧ (Finite3LinSource.ofActual I).badRow x e = true
        then (1 : ℝ) else 0 := by
  unfold questionFailIndicator
  split
  · rename_i hex
    obtain ⟨e, he, hb⟩ := hex
    have hterm :
        (if e ∈ P.U ∧ (Finite3LinSource.ofActual I).badRow x e = true
          then (1 : ℝ) else 0) = 1 := by
      simp [he, hb]
    calc
      (1 : ℝ) = (if e ∈ P.U ∧ (Finite3LinSource.ofActual I).badRow x e = true
          then (1 : ℝ) else 0) := hterm.symm
      _ ≤ ∑ q : I.RowId,
          if q ∈ P.U ∧ (Finite3LinSource.ofActual I).badRow x q = true
            then (1 : ℝ) else 0 :=
        Finset.single_le_sum
          (fun q _ => questionFailTerm_nonneg P x q) (Finset.mem_univ e)
  · exact Finset.sum_nonneg fun q _ => questionFailTerm_nonneg P x q

private theorem ofActual_sourceExtension_original_bad
    (y : Fin N → ZMod 2) (r : Fin m) :
    (Finite3LinSource.ofActual I).badRow (I.sourceExtension y) (Sum.inl r) =
      I.sourceBadRow y r := by
  rw [Finite3LinSource.ofActual_badRow]
  exact I.sourceExtension_original_bad y r

theorem questionFail_sourceExtension_original
    (I : ActualOccurrenceAllocation.Instance N m)
    (P : PresentedLeaf I J h)
    (hU : ∀ e ∈ P.U, ∃ r : Fin m, e = Sum.inl r)
    (y : Fin N → ZMod 2) :
    questionFailIndicator P (I.sourceExtension y) =
      if ∃ e ∈ P.U, ∃ r : Fin m, e = Sum.inl r ∧ I.sourceBadRow y r = true
        then 1 else 0 := by
  unfold questionFailIndicator
  have hiff :
      (∃ e ∈ P.U,
          (Finite3LinSource.ofActual I).badRow (I.sourceExtension y) e = true) ↔
        (∃ e ∈ P.U, ∃ r : Fin m, e = Sum.inl r ∧ I.sourceBadRow y r = true) := by
    constructor
    · rintro ⟨e, he, hb⟩
      obtain ⟨r, hr⟩ := hU e he
      refine ⟨e, he, r, hr, ?_⟩
      subst e
      rwa [ofActual_sourceExtension_original_bad] at hb
    · rintro ⟨e, he, r, hr, hb⟩
      refine ⟨e, he, ?_⟩
      subst e
      rwa [ofActual_sourceExtension_original_bad]
  by_cases hp :
      ∃ e ∈ P.U,
        (Finite3LinSource.ofActual I).badRow (I.sourceExtension y) e = true
  · rw [ite_eq_left hp, ite_eq_left (hiff.mp hp)]
  · rw [ite_eq_right hp, ite_eq_right (hiff.not.mp hp)]

noncomputable def anyQuestionFailIndicator
    {n : Nat} (Ps : Fin n → PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) : ℝ :=
  if ∃ i, questionFailIndicator (Ps i) x = 1 then 1 else 0

theorem anyQuestionFailIndicator_le_sum
    {n : Nat} (Ps : Fin n → PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    anyQuestionFailIndicator Ps x ≤
      ∑ i : Fin n, questionFailIndicator (Ps i) x := by
  unfold anyQuestionFailIndicator
  split
  · rename_i hex
    obtain ⟨i, hi⟩ := hex
    calc
      (1 : ℝ) = questionFailIndicator (Ps i) x := hi.symm
      _ ≤ ∑ j : Fin n, questionFailIndicator (Ps j) x :=
        Finset.single_le_sum
          (fun j _ => questionFailIndicator_nonneg (Ps j) x)
          (Finset.mem_univ i)
  · exact Finset.sum_nonneg fun i _ => questionFailIndicator_nonneg (Ps i) x

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
