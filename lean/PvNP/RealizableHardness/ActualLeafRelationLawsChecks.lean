import PvNP.RealizableHardness.ActualLeafRelationLaws

namespace PvNP.RealizableHardness.ActualLeafRelationLawsChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section

#check row_private_outside_two_questions
#check equationSpan_inf_sup_coordinateSpace_le
#check actual_equationSpan_inf_sup_coordinateSpace_le
#check PresentedLeaf.Rel.refl
#check PresentedLeaf.Rel.symm
#check PresentedLeaf.Rel.trans
#check transportCompatible_refl
#check transportedLabel_identity_canonical
#check transportCompatible_symm
#check transportedLabel_inverse_canonical
#check transportedLabel_proof_irrel

#print axioms row_private_outside_two_questions
#print axioms equationSpan_inf_sup_coordinateSpace_le
#print axioms actual_equationSpan_inf_sup_coordinateSpace_le
#print axioms PresentedLeaf.Rel.refl
#print axioms PresentedLeaf.Rel.symm
#print axioms PresentedLeaf.Rel.trans
#print axioms transportCompatible_refl
#print axioms transportedLabel_identity_canonical
#print axioms transportCompatible_symm
#print axioms transportedLabel_inverse_canonical
#print axioms transportedLabel_proof_irrel

local instance relationLawsChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

/-! Three genuinely distinct original-row questions exercise actual incidence
transitivity, while a distinct pair exercises canonical inverse transport. -/

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

theorem three_questions_distinct :
    (originalPresented 0).U ≠ (originalPresented 1).U ∧
    (originalPresented 1).U ≠ (originalPresented 2).U ∧
    (originalPresented 0).U ≠ (originalPresented 2).U := by
  simp [originalPresented, originalQuestion]

example : (originalPresented 0).Rel (originalPresented 2) := by
  exact PresentedLeaf.Rel.trans (originalPresented 0) (originalPresented 1)
    (originalPresented 2) (original_rel 0 1) (original_rel 1 2)

def sourceCoordinateFunctional :
    coordinateSpace threeRowActual.support (originalQuestion 0) →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose
    (actual_exists_coordinateFunctional threeRowActual (originalQuestion 0)
      (originalQuestion_good 0))

theorem sourceCoordinateFunctional_rhs :
    ∀ e (he : e ∈ originalQuestion 0),
      sourceCoordinateFunctional
        ⟨equationVector threeRowActual.support e,
          equationVector_mem_coordinateSpace threeRowActual.support
            (originalQuestion 0) e he⟩ =
        threeRowActual.rowRhs e :=
  Classical.choose_spec
    (actual_exists_coordinateFunctional threeRowActual (originalQuestion 0)
      (originalQuestion_good 0))

def sourceLabel : RawLeafLabel threeRowActual (originalPresented 0).domain :=
  sourceCoordinateFunctional.comp
    (Submodule.inclusion (originalPresented 0).domain_le_coordinateSpace)

theorem sourceLabel_respects :
    RespectsAt (originalPresented 0) rfl sourceLabel := by
  intro e he
  change sourceCoordinateFunctional
      ⟨equationVector threeRowActual.support e, _⟩ =
    threeRowActual.rowRhs e
  exact sourceCoordinateFunctional_rhs e he

example :
    transportedLabel (originalPresented 0) (originalPresented 0)
        (PresentedLeaf.Rel.refl (originalPresented 0))
        sourceLabel sourceLabel_respects = sourceLabel := by
  exact transportedLabel_identity_canonical
    (originalPresented 0) sourceLabel sourceLabel_respects

example :
    transportedLabel (originalPresented 1) (originalPresented 0)
        (PresentedLeaf.Rel.symm (original_rel 0 1))
        (transportedLabel (originalPresented 0) (originalPresented 1)
          (original_rel 0 1) sourceLabel sourceLabel_respects)
        (transportedLabel_respectsAt (originalPresented 0) (originalPresented 1)
          (original_rel 0 1) sourceLabel sourceLabel_respects) = sourceLabel := by
  exact transportedLabel_inverse_canonical (originalPresented 0)
    (originalPresented 1) (original_rel 0 1) sourceLabel sourceLabel_respects

/-! The empty-question boundary checks identity, inverse, and transitivity in
dimension zero independently from the nonempty three-question fixture. -/

def emptyPresented {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : PresentedLeaf I 0 0 where
  U := ∅
  goodU := by simp [GoodQuestion]
  card_U := by simp
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

def zeroRawLeafLabel {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    RawLeafLabel I (emptyPresented I).domain := by
  change (emptyPresented I).domain →ₗ[ZMod 2] ZMod 2
  exact 0

theorem zeroRawLeafLabel_respects {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    RespectsAt (emptyPresented I) rfl (zeroRawLeafLabel I) := by
  intro e he
  simp [emptyPresented] at he

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    (emptyPresented I).Rel (emptyPresented I) :=
  PresentedLeaf.Rel.refl (emptyPresented I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    transportedLabel (emptyPresented I) (emptyPresented I)
        (PresentedLeaf.Rel.refl (emptyPresented I))
        (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I) =
      zeroRawLeafLabel I := by
  exact transportedLabel_identity_canonical (emptyPresented I)
    (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    transportedLabel (emptyPresented I) (emptyPresented I)
        (PresentedLeaf.Rel.symm (PresentedLeaf.Rel.refl (emptyPresented I)))
        (transportedLabel (emptyPresented I) (emptyPresented I)
          (PresentedLeaf.Rel.refl (emptyPresented I))
          (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I))
        (transportedLabel_respectsAt (emptyPresented I) (emptyPresented I)
          (PresentedLeaf.Rel.refl (emptyPresented I))
          (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)) =
      zeroRawLeafLabel I := by
  exact transportedLabel_inverse_canonical (emptyPresented I)
    (emptyPresented I) (PresentedLeaf.Rel.refl (emptyPresented I))
      (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    (emptyPresented I).Rel (emptyPresented I) := by
  exact PresentedLeaf.Rel.trans (emptyPresented I) (emptyPresented I)
    (emptyPresented I) (PresentedLeaf.Rel.refl (emptyPresented I))
      (PresentedLeaf.Rel.refl (emptyPresented I))

end
end PvNP.RealizableHardness.ActualLeafRelationLawsChecks
