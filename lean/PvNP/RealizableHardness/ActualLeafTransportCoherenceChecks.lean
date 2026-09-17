import PvNP.RealizableHardness.ActualLeafTransportCoherence

namespace PvNP.RealizableHardness.ActualLeafTransportCoherenceChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section

#check equationVectors_threeGoodQuestions_linearIndependent
#check actual_existsUnique_rhsFunctional_threeGoodQuestions
#check domain_inf_twoEquationSpans_le
#check actual_existsUnique_threeWayGluedLeafRhsFunctional
#check transportedLabel_coherence

#print axioms equationVectors_threeGoodQuestions_linearIndependent
#print axioms actual_existsUnique_rhsFunctional_threeGoodQuestions
#print axioms domain_inf_twoEquationSpans_le
#print axioms actual_existsUnique_threeWayGluedLeafRhsFunctional
#print axioms transportedLabel_coherence

local instance coherenceChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

/-! Three distinct actual original-row questions exercise sequential versus
direct transport with a nonzero source RHS. -/

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
            (originalQuestion 0) e he⟩ = threeRowActual.rowRhs e :=
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
      ⟨equationVector threeRowActual.support e, _⟩ = threeRowActual.rowRhs e
  exact sourceCoordinateFunctional_rhs e he

theorem three_questions_distinct :
    (originalPresented 0).U ≠ (originalPresented 1).U ∧
    (originalPresented 1).U ≠ (originalPresented 2).U ∧
    (originalPresented 0).U ≠ (originalPresented 2).U := by
  simp [originalPresented, originalQuestion]

example :
    transportedLabel (originalPresented 1) (originalPresented 2)
        (original_rel 1 2)
        (transportedLabel (originalPresented 0) (originalPresented 1)
          (original_rel 0 1) sourceLabel sourceLabel_respects)
        (transportedLabel_respectsAt (originalPresented 0)
          (originalPresented 1) (original_rel 0 1)
          sourceLabel sourceLabel_respects) =
      transportedLabel (originalPresented 0) (originalPresented 2)
        (PresentedLeaf.Rel.trans (originalPresented 0) (originalPresented 1)
          (originalPresented 2) (original_rel 0 1) (original_rel 1 2))
        sourceLabel sourceLabel_respects := by
  exact transportedLabel_coherence (originalPresented 0)
    (originalPresented 1) (originalPresented 2)
    (original_rel 0 1) (original_rel 1 2) sourceLabel sourceLabel_respects

/-! The first row occurs in two presentations. The union theorem therefore
deduplicates one RowId while retaining its single actual `rowRhs`. -/

example :
    ∃! psi : equationSpan threeRowActual.support
        ((originalPresented 0).U ∪ (originalPresented 0).U ∪
          (originalPresented 1).U) →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ (originalPresented 0).U ∪ (originalPresented 0).U ∪
          (originalPresented 1).U),
        psi ⟨equationVector threeRowActual.support e,
          equationVector_mem_equationSpan threeRowActual.support
            ((originalPresented 0).U ∪ (originalPresented 0).U ∪
              (originalPresented 1).U) e he⟩ = threeRowActual.rowRhs e := by
  exact actual_existsUnique_rhsFunctional_threeGoodQuestions threeRowActual
    (originalPresented 0) (originalPresented 0) (originalPresented 1)

/-! The empty boundary exercises all quantifiers with the zero carrier. -/

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
    transportedLabel (emptyPresented I) (emptyPresented I)
        (PresentedLeaf.Rel.refl (emptyPresented I))
        (transportedLabel (emptyPresented I) (emptyPresented I)
          (PresentedLeaf.Rel.refl (emptyPresented I))
          (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I))
        (transportedLabel_respectsAt (emptyPresented I) (emptyPresented I)
          (PresentedLeaf.Rel.refl (emptyPresented I))
          (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)) =
      transportedLabel (emptyPresented I) (emptyPresented I)
        (PresentedLeaf.Rel.trans (emptyPresented I) (emptyPresented I)
          (emptyPresented I) (PresentedLeaf.Rel.refl (emptyPresented I))
          (PresentedLeaf.Rel.refl (emptyPresented I)))
        (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I) := by
  exact transportedLabel_coherence (emptyPresented I) (emptyPresented I)
    (emptyPresented I) (PresentedLeaf.Rel.refl (emptyPresented I))
    (PresentedLeaf.Rel.refl (emptyPresented I))
    (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)

end
end PvNP.RealizableHardness.ActualLeafTransportCoherenceChecks
