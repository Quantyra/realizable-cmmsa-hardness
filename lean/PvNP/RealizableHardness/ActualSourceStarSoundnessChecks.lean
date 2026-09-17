import PvNP.RealizableHardness.ActualSourceStarSoundness

namespace PvNP.RealizableHardness.ActualSourceStarSoundnessChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualQuestionMassBridge
open scoped BigOperators
noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#check questionFailIndicator
#check questionFailIndicator_nonneg
#check questionFailIndicator_le_one
#check questionFailIndicator_eq_zero_iff
#check questionFailIndicator_eq_one_iff
#check presentedEnum
#check presentedEnum_mem
#check presentedEnum_surj
#check questionFailIndicator_eq_baseFailure
#check questionFailIndicator_le_sum
#check questionFail_sourceExtension_original
#check anyQuestionFailIndicator
#check anyQuestionFailIndicator_le_sum

#print axioms questionFailIndicator_nonneg
#print axioms questionFailIndicator_le_one
#print axioms questionFailIndicator_eq_zero_iff
#print axioms questionFailIndicator_eq_one_iff
#print axioms presentedEnum_mem
#print axioms presentedEnum_surj
#print axioms questionFailIndicator_eq_baseFailure
#print axioms questionFailIndicator_le_sum
#print axioms questionFail_sourceExtension_original
#print axioms anyQuestionFailIndicator_le_sum

local instance sourceStarSoundnessChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance sourceStarSoundnessChecksGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

/-! Three distinct actual original-row questions with mixed RHS. The assignment
sets the unique nonzero-RHS original support bit and is zero elsewhere. -/

def threeRowActual : ActualOccurrenceAllocation.Instance 1 3 where
  vars := fun _ _ => 0
  rhs := fun r => if r = 0 then 1 else 0

def originalQuestion (r : Fin 3) : Finset threeRowActual.RowId :=
  {Sum.inl r}

theorem originalQuestion_good (r : Fin 3) :
    GoodQuestion threeRowActual.support (originalQuestion r) := by
  simp [GoodQuestion, originalQuestion]

def originalPresented (r : Fin 3) : PresentedLeaf threeRowActual 1 0 where
  U := originalQuestion r
  goodU := originalQuestion_good r
  card_U := by simp [originalQuestion]
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

theorem original_mem (r : Fin 3) : Sum.inl r ∈ (originalPresented r).U := by
  simp [originalPresented, originalQuestion]

theorem originalPresented_original (r : Fin 3) :
    ∀ e ∈ (originalPresented r).U, ∃ s : Fin 3, e = Sum.inl s := by
  intro e he
  refine ⟨r, ?_⟩
  simpa [originalPresented, originalQuestion] using he

def honestAssignment : threeRowActual.GlobalVar → ZMod 2 :=
  fun v => if v = threeRowActual.originalRow 0 0 then 1 else 0

theorem honestAssignment_original00 :
    honestAssignment (threeRowActual.originalRow 0 0) = 1 := by
  simp [honestAssignment]

theorem honestAssignment_original_ne {r i : Fin 3} (h : ¬ (r = 0 ∧ i = 0)) :
    honestAssignment (threeRowActual.originalRow r i) = 0 := by
  simp only [honestAssignment, ite_eq_right_iff, one_ne_zero, imp_false]
  intro heq
  exact h ⟨congrArg Prod.fst (threeRowActual.anchor_injective heq),
    congrArg Prod.snd (threeRowActual.anchor_injective heq)⟩

theorem honestAssignment_satisfies_original (r : Fin 3) :
    honestAssignment (threeRowActual.originalRow r 0)
      + honestAssignment (threeRowActual.originalRow r 1)
      + honestAssignment (threeRowActual.originalRow r 2) =
      threeRowActual.rhs r := by
  have hrhs : threeRowActual.rhs r = if r = 0 then (1 : ZMod 2) else 0 := rfl
  rw [hrhs]
  by_cases hr : r = 0
  · subst r
    rw [honestAssignment_original00]
    rw [honestAssignment_original_ne (by decide : ¬ ((0 : Fin 3) = 0 ∧ (1 : Fin 3) = 0))]
    rw [honestAssignment_original_ne (by decide : ¬ ((0 : Fin 3) = 0 ∧ (2 : Fin 3) = 0))]
    rfl
  · have h0 : ¬ (r = 0 ∧ (0 : Fin 3) = 0) := fun h => hr h.1
    have h1 : ¬ (r = 0 ∧ (1 : Fin 3) = 0) := fun h => hr h.1
    have h2 : ¬ (r = 0 ∧ (2 : Fin 3) = 0) := fun h => hr h.1
    rw [honestAssignment_original_ne h0, honestAssignment_original_ne h1,
      honestAssignment_original_ne h2]
    simp [hr]

theorem honestAssignment_badRow_false (r : Fin 3) :
    (Finite3LinSource.ofActual threeRowActual).badRow honestAssignment
      (Sum.inl r) = false := by
  unfold Finite3LinSource.badRow
  rw [Finite3LinSource.ofActual_row, Finite3LinSource.ofActual_row,
    Finite3LinSource.ofActual_row, Finite3LinSource.ofActual_rhs]
  have h : honestAssignment (threeRowActual.row (Sum.inl r) 0)
      + honestAssignment (threeRowActual.row (Sum.inl r) 1)
      + honestAssignment (threeRowActual.row (Sum.inl r) 2) =
      threeRowActual.rowRhs (Sum.inl r) :=
    honestAssignment_satisfies_original r
  simp [h]

theorem honestAssignment_respects (r : Fin 3) :
    RespectsAt (originalPresented r) rfl
      (honestRawLabel (D := (originalPresented r).domain) honestAssignment) := by
  rw [honestRawLabel_respects_iff]
  intro e he
  have heq : e = Sum.inl r := by
    simpa [originalPresented, originalQuestion] using he
  simpa [heq] using honestAssignment_badRow_false r

def violatingAssignment : threeRowActual.GlobalVar → ZMod 2 :=
  fun _ => 0

theorem violatingAssignment_badRow_true :
    (Finite3LinSource.ofActual threeRowActual).badRow violatingAssignment
      (Sum.inl 0) = true := by
  unfold Finite3LinSource.badRow
  rw [Finite3LinSource.ofActual_row, Finite3LinSource.ofActual_row,
    Finite3LinSource.ofActual_row, Finite3LinSource.ofActual_rhs]
  simp [violatingAssignment, threeRowActual,
    ActualOccurrenceAllocation.Instance.rowRhs]

theorem violatingAssignment_not_respects :
    ¬ RespectsAt (originalPresented 0) rfl
      (honestRawLabel (D := (originalPresented 0).domain) violatingAssignment) := by
  rw [honestRawLabel_respects_iff]
  intro h
  have := h (Sum.inl 0) (original_mem 0)
  rw [violatingAssignment_badRow_true] at this
  exact Bool.false_ne_true this.symm

example :
    questionFailIndicator (originalPresented 0) honestAssignment = 0 ↔
      RespectsAt (originalPresented 0) rfl
        (honestRawLabel (D := (originalPresented 0).domain) honestAssignment) :=
  questionFailIndicator_eq_zero_iff (originalPresented 0) honestAssignment

example :
    questionFailIndicator (originalPresented 0) honestAssignment = 0 :=
  (questionFailIndicator_eq_zero_iff (originalPresented 0) honestAssignment).mpr
    (honestAssignment_respects 0)

example :
    questionFailIndicator (originalPresented 0) violatingAssignment = 1 ↔
      ¬ RespectsAt (originalPresented 0) rfl
        (honestRawLabel (D := (originalPresented 0).domain) violatingAssignment) :=
  questionFailIndicator_eq_one_iff (originalPresented 0) violatingAssignment

example :
    questionFailIndicator (originalPresented 0) violatingAssignment = 1 :=
  (questionFailIndicator_eq_one_iff (originalPresented 0) violatingAssignment).mpr
    violatingAssignment_not_respects

example :
    questionFailIndicator (originalPresented 0) honestAssignment =
      actualBaseFailureIndicator threeRowActual honestAssignment
        (presentedEnum (originalPresented 0)) :=
  questionFailIndicator_eq_baseFailure (originalPresented 0) honestAssignment

example :
    questionFailIndicator (originalPresented 0) violatingAssignment =
      actualBaseFailureIndicator threeRowActual violatingAssignment
        (presentedEnum (originalPresented 0)) :=
  questionFailIndicator_eq_baseFailure (originalPresented 0) violatingAssignment

example :
    questionFailIndicator (originalPresented 0) honestAssignment ≤
      ∑ e : threeRowActual.RowId,
        if e ∈ (originalPresented 0).U ∧
            (Finite3LinSource.ofActual threeRowActual).badRow honestAssignment e =
              true
          then (1 : ℝ) else 0 :=
  questionFailIndicator_le_sum (originalPresented 0) honestAssignment

example :
    questionFailIndicator (originalPresented 0) violatingAssignment ≤
      ∑ e : threeRowActual.RowId,
        if e ∈ (originalPresented 0).U ∧
            (Finite3LinSource.ofActual threeRowActual).badRow violatingAssignment e =
              true
          then (1 : ℝ) else 0 :=
  questionFailIndicator_le_sum (originalPresented 0) violatingAssignment

example :
    presentedEnum (originalPresented 0) 0 ∈ (originalPresented 0).U :=
  presentedEnum_mem (originalPresented 0) 0

example :
    ∃ i : Fin 1, presentedEnum (originalPresented 0) i = Sum.inl 0 :=
  presentedEnum_surj (originalPresented 0) (Sum.inl 0) (original_mem 0)

def sourceY0 : Fin 1 → ZMod 2 := fun _ => 0

example :
    questionFailIndicator (originalPresented 0)
        (threeRowActual.sourceExtension sourceY0) =
      if ∃ e ∈ (originalPresented 0).U, ∃ r : Fin 3,
          e = Sum.inl r ∧ threeRowActual.sourceBadRow sourceY0 r = true
        then 1 else 0 :=
  questionFail_sourceExtension_original threeRowActual (originalPresented 0)
    (originalPresented_original 0) sourceY0

def onePresented : Fin 1 → PresentedLeaf threeRowActual 1 0 :=
  fun _ => originalPresented 0

def twoPresented (i : Fin 2) : PresentedLeaf threeRowActual 1 0 :=
  originalPresented (i.castLE (by decide))

example :
    anyQuestionFailIndicator onePresented honestAssignment ≤
      ∑ i : Fin 1, questionFailIndicator (onePresented i) honestAssignment :=
  anyQuestionFailIndicator_le_sum onePresented honestAssignment

example :
    anyQuestionFailIndicator onePresented violatingAssignment ≤
      ∑ i : Fin 1, questionFailIndicator (onePresented i) violatingAssignment :=
  anyQuestionFailIndicator_le_sum onePresented violatingAssignment

example :
    anyQuestionFailIndicator twoPresented honestAssignment ≤
      ∑ i : Fin 2, questionFailIndicator (twoPresented i) honestAssignment :=
  anyQuestionFailIndicator_le_sum twoPresented honestAssignment

example :
    anyQuestionFailIndicator twoPresented violatingAssignment ≤
      ∑ i : Fin 2, questionFailIndicator (twoPresented i) violatingAssignment :=
  anyQuestionFailIndicator_le_sum twoPresented violatingAssignment

/-! Empty `J = h = 0` boundary. -/

def emptyPresented {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : PresentedLeaf I 0 0 where
  U := ∅
  goodU := by simp [GoodQuestion]
  card_U := by simp
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

def zeroAssignment {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    I.GlobalVar → ZMod 2 := fun _ => 0

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2) :
    questionFailIndicator (emptyPresented I) x = 0 := by
  unfold questionFailIndicator
  simp [emptyPresented]

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    questionFailIndicator (emptyPresented I) (zeroAssignment I) =
      actualBaseFailureIndicator I (zeroAssignment I)
        (presentedEnum (emptyPresented I)) :=
  questionFailIndicator_eq_baseFailure (emptyPresented I) (zeroAssignment I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    questionFailIndicator (emptyPresented I) (zeroAssignment I) = 0 ↔
      RespectsAt (emptyPresented I) rfl
        (honestRawLabel (D := (emptyPresented I).domain) (zeroAssignment I)) :=
  questionFailIndicator_eq_zero_iff (emptyPresented I) (zeroAssignment I)

end
end PvNP.RealizableHardness.ActualSourceStarSoundnessChecks
