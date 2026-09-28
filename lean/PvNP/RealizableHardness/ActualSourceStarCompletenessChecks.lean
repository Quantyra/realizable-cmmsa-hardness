import PvNP.RealizableHardness.ActualSourceStarCompleteness

namespace PvNP.RealizableHardness.ActualSourceStarCompletenessChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#check honestRawLabel
#check honestRawLabel_eval_equation
#check honestRawLabel_respects_iff
#check honestPackaged
#check restrictionAgreesOnCenter_honest
#check starAccepts_honest

#print axioms honestRawLabel_eval_equation
#print axioms honestRawLabel_respects_iff
#print axioms restrictionAgreesOnCenter_honest
#print axioms starAccepts_honest

local instance sourceStarChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance sourceStarChecksGlobalVarDecidableEq {N m : Nat}
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

theorem original_rel (r s : Fin 3) :
    (originalPresented r).Rel (originalPresented s) := by
  simp [PresentedLeaf.Rel, PresentedLeaf.domain, originalPresented, sup_comm]

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

theorem original_mem (r : Fin 3) : Sum.inl r ∈ (originalPresented r).U := by
  simp [originalPresented, originalQuestion]

theorem honestAssignment_respects (r : Fin 3) :
    RespectsAt (originalPresented r) rfl
      (honestRawLabel (D := (originalPresented r).domain) honestAssignment) := by
  rw [honestRawLabel_respects_iff]
  intro e he
  have heq : e = Sum.inl r := by
    simpa [originalPresented, originalQuestion] using he
  simpa [heq] using honestAssignment_badRow_false r

def presentedCenter (r : Fin 3) :
    CenterSubspace ⟨(originalPresented r).domain, ⟨originalPresented r, rfl⟩⟩ 0 where
  K := ⊥
  le_domain := bot_le
  transverse := by simp
  finrank := by simp

example :
    (honestRawLabel (D := (originalPresented 0).domain) honestAssignment).toFun
      ⟨equationVector threeRowActual.support (Sum.inl 0),
        (originalPresented 0).H_le_domain
          (equationVector_mem_equationSpan threeRowActual.support
            (originalPresented 0).U (Sum.inl 0) (original_mem 0))⟩ =
      honestAssignment (threeRowActual.row (Sum.inl 0) 0)
        + honestAssignment (threeRowActual.row (Sum.inl 0) 1)
        + honestAssignment (threeRowActual.row (Sum.inl 0) 2) :=
  honestRawLabel_eval_equation (originalPresented 0) honestAssignment
    (Sum.inl 0) (original_mem 0)

example :
    RespectsAt (originalPresented 0) rfl
      (honestRawLabel (D := (originalPresented 0).domain) honestAssignment) ↔
      ∀ e ∈ (originalPresented 0).U,
        (Finite3LinSource.ofActual threeRowActual).badRow honestAssignment e =
          false :=
  honestRawLabel_respects_iff (originalPresented 0) honestAssignment

example :
    RespectsAt (originalPresented 1) rfl
      (honestRawLabel (D := (originalPresented 1).domain) honestAssignment) ↔
      ∀ e ∈ (originalPresented 1).U,
        (Finite3LinSource.ofActual threeRowActual).badRow honestAssignment e =
          false :=
  honestRawLabel_respects_iff (originalPresented 1) honestAssignment

example :
    restrictionAgreesOnCenter
      ((LeafVertex.Rel_iff_presented _ _ (originalPresented 0) (originalPresented 1)
        rfl rfl).mpr (original_rel 0 1))
      (presentedCenter 0) (presentedCenter 1) rfl
      (honestPackaged (originalPresented 0) honestAssignment
        (honestAssignment_respects 0))
      (honestPackaged (originalPresented 1) honestAssignment
        (honestAssignment_respects 1)) :=
  restrictionAgreesOnCenter_honest
    (originalPresented 0) (originalPresented 1) (original_rel 0 1)
    honestAssignment (honestAssignment_respects 0) (honestAssignment_respects 1)
    (presentedCenter 0) (presentedCenter 1) rfl

def onePresented : Fin 1 → PresentedLeaf threeRowActual 1 0 :=
  fun _ => originalPresented 0

def oneCenter (i : Fin 1) :
    CenterSubspace ⟨(onePresented i).domain, ⟨onePresented i, rfl⟩⟩ 0 :=
  presentedCenter 0

example :
    starAccepts
      (fun i : Fin 1 => ⟨(onePresented i).domain, ⟨onePresented i, rfl⟩⟩)
      (fun i : Fin 1 => ⟨(onePresented i).domain, ⟨onePresented i, rfl⟩⟩)
      (fun i => LeafVertex.Rel.refl _)
      oneCenter oneCenter (fun i => rfl)
      (fun i => honestPackaged (onePresented i) honestAssignment
        (honestAssignment_respects 0))
      (fun i => honestPackaged (onePresented i) honestAssignment
        (honestAssignment_respects 0)) :=
  starAccepts_honest onePresented honestAssignment
    (fun _ => honestAssignment_respects 0) oneCenter (fun _ _ => rfl)

def twoPresented (i : Fin 2) : PresentedLeaf threeRowActual 1 0 :=
  originalPresented (i.castLE (by decide))

def twoCenter (i : Fin 2) :
    CenterSubspace ⟨(twoPresented i).domain, ⟨twoPresented i, rfl⟩⟩ 0 where
  K := ⊥
  le_domain := bot_le
  transverse := by simp
  finrank := by simp

theorem twoPresented_respects (i : Fin 2) :
    RespectsAt (twoPresented i) rfl
      (honestRawLabel (D := (twoPresented i).domain) honestAssignment) :=
  honestAssignment_respects (i.castLE (by decide))

example :
    starAccepts
      (fun i : Fin 2 => ⟨(twoPresented i).domain, ⟨twoPresented i, rfl⟩⟩)
      (fun i : Fin 2 => ⟨(twoPresented i).domain, ⟨twoPresented i, rfl⟩⟩)
      (fun i => LeafVertex.Rel.refl _)
      twoCenter twoCenter (fun i => rfl)
      (fun i => honestPackaged (twoPresented i) honestAssignment
        (twoPresented_respects i))
      (fun i => honestPackaged (twoPresented i) honestAssignment
        (twoPresented_respects i)) :=
  starAccepts_honest twoPresented honestAssignment twoPresented_respects
    twoCenter (fun _ _ => rfl)

/-! Empty `J = h = 0` boundary with the zero assignment. -/

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

theorem zeroAssignment_respects {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    RespectsAt (emptyPresented I) rfl
      (honestRawLabel (D := (emptyPresented I).domain) (zeroAssignment I)) := by
  intro e he
  simp [emptyPresented] at he

def emptyCenter {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    CenterSubspace ⟨(emptyPresented I).domain, ⟨emptyPresented I, rfl⟩⟩ 0 where
  K := ⊥
  le_domain := bot_le
  transverse := by simp
  finrank := by simp

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    RespectsAt (emptyPresented I) rfl
      (honestRawLabel (D := (emptyPresented I).domain) (zeroAssignment I)) ↔
      ∀ e ∈ (emptyPresented I).U,
        (Finite3LinSource.ofActual I).badRow (zeroAssignment I) e = false :=
  honestRawLabel_respects_iff (emptyPresented I) (zeroAssignment I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    restrictionAgreesOnCenter
      ((LeafVertex.Rel_iff_presented _ _ (emptyPresented I) (emptyPresented I)
        rfl rfl).mpr rfl)
      (emptyCenter I) (emptyCenter I) rfl
      (honestPackaged (emptyPresented I) (zeroAssignment I)
        (zeroAssignment_respects I))
      (honestPackaged (emptyPresented I) (zeroAssignment I)
        (zeroAssignment_respects I)) :=
  restrictionAgreesOnCenter_honest (emptyPresented I) (emptyPresented I) rfl
    (zeroAssignment I) (zeroAssignment_respects I) (zeroAssignment_respects I)
    (emptyCenter I) (emptyCenter I) rfl

def emptyFamily {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    Fin 1 → PresentedLeaf I 0 0 :=
  fun _ => emptyPresented I

def emptyFamilyCenter {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (i : Fin 1) :
    CenterSubspace ⟨(emptyFamily I i).domain, ⟨emptyFamily I i, rfl⟩⟩ 0 :=
  emptyCenter I

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    starAccepts
      (fun i : Fin 1 => ⟨(emptyFamily I i).domain, ⟨emptyFamily I i, rfl⟩⟩)
      (fun i : Fin 1 => ⟨(emptyFamily I i).domain, ⟨emptyFamily I i, rfl⟩⟩)
      (fun i => LeafVertex.Rel.refl _)
      (emptyFamilyCenter I) (emptyFamilyCenter I) (fun i => rfl)
      (fun i => honestPackaged (emptyFamily I i) (zeroAssignment I)
        (zeroAssignment_respects I))
      (fun i => honestPackaged (emptyFamily I i) (zeroAssignment I)
        (zeroAssignment_respects I)) :=
  starAccepts_honest (emptyFamily I) (zeroAssignment I)
    (fun _ => zeroAssignment_respects I) (emptyFamilyCenter I) (fun _ _ => rfl)

end
end PvNP.RealizableHardness.ActualSourceStarCompletenessChecks
