import PvNP.RealizableHardness.ActualLeafTransport

namespace PvNP.RealizableHardness.ActualLeafTransportChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section

#check PresentedLeaf.Rel
#check PresentedLeaf.rightDomain_le_common
#check TransportCompatible
#check transportedLabel
#check transportedLabel_respectsAt
#check transportedLabel_compatible
#check transportedLabel_unique
#check existsUnique_compatibleTransport

#print axioms PresentedLeaf.rightDomain_le_common
#print axioms transportedLabel_respectsAt
#print axioms transportedLabel_compatible
#print axioms transportedLabel_unique
#print axioms existsUnique_compatibleTransport

local instance leafTransportChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

/-! The nonempty fixture transports between two genuinely distinct original
questions.  With `L = ⊥`, the common-domain relation is the commutativity of
the two equation-space joins; the target type is therefore not definitionally
the source label type. -/

def twoRowActual : ActualOccurrenceAllocation.Instance 1 2 where
  vars := fun _ _ => 0
  rhs := fun r => if r = 0 then 1 else 0

def sourceU : Finset twoRowActual.RowId := {Sum.inl 0}
def targetU : Finset twoRowActual.RowId := {Sum.inl 1}

theorem sourceU_good : GoodQuestion twoRowActual.support sourceU := by
  simp [GoodQuestion, sourceU]

theorem targetU_good : GoodQuestion twoRowActual.support targetU := by
  simp [GoodQuestion, targetU]

def sourcePresented : PresentedLeaf twoRowActual 1 0 where
  U := sourceU
  goodU := sourceU_good
  card_U := by simp [sourceU]
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

def targetPresented : PresentedLeaf twoRowActual 1 0 where
  U := targetU
  goodU := targetU_good
  card_U := by simp [targetU]
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

theorem source_target_questions_distinct :
    sourcePresented.U ≠ targetPresented.U := by
  simp [sourcePresented, targetPresented, sourceU, targetU]

theorem source_target_rel : sourcePresented.Rel targetPresented := by
  simp [PresentedLeaf.Rel, PresentedLeaf.domain, sourcePresented,
    targetPresented, sup_comm]

def sourceCoordinateFunctional :
    coordinateSpace twoRowActual.support sourceU →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose
    (actual_exists_coordinateFunctional twoRowActual sourceU sourceU_good)

theorem sourceCoordinateFunctional_rhs :
    ∀ e (he : e ∈ sourceU),
      sourceCoordinateFunctional
        ⟨equationVector twoRowActual.support e,
          equationVector_mem_coordinateSpace twoRowActual.support sourceU e he⟩ =
        twoRowActual.rowRhs e :=
  (Classical.choose_spec
    (actual_exists_coordinateFunctional twoRowActual sourceU sourceU_good))

def sourceLabel : RawLeafLabel twoRowActual sourcePresented.domain :=
  sourceCoordinateFunctional.comp
    (Submodule.inclusion sourcePresented.domain_le_coordinateSpace)

theorem sourceLabel_respects :
    RespectsAt sourcePresented rfl sourceLabel := by
  intro e he
  change sourceCoordinateFunctional
      ⟨equationVector twoRowActual.support e, _⟩ =
    twoRowActual.rowRhs e
  exact sourceCoordinateFunctional_rhs e he

example :
    ∃! g : RawLeafLabel twoRowActual targetPresented.domain,
      RespectsAt targetPresented rfl g ∧
        TransportCompatible sourcePresented targetPresented source_target_rel
          sourceLabel g := by
  exact existsUnique_compatibleTransport
    sourcePresented targetPresented source_target_rel sourceLabel
      sourceLabel_respects

example :
    RespectsAt targetPresented rfl
      (transportedLabel sourcePresented targetPresented source_target_rel
        sourceLabel sourceLabel_respects) := by
  exact transportedLabel_respectsAt
    sourcePresented targetPresented source_target_rel sourceLabel
      sourceLabel_respects

/-! Empty questions exercise the zero-dimensional boundary without relying on
the nonempty fixture. -/

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
    (I : ActualOccurrenceAllocation.Instance N m)
    (D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)) : RawLeafLabel I D :=
  by
    change D →ₗ[ZMod 2] ZMod 2
    exact 0

theorem empty_rel {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    (emptyPresented I).Rel (emptyPresented I) := by
  rfl

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    ∃! g : RawLeafLabel I (emptyPresented I).domain,
      RespectsAt (emptyPresented I) rfl g ∧
        TransportCompatible (emptyPresented I) (emptyPresented I) (empty_rel I)
          (zeroRawLeafLabel I (emptyPresented I).domain) g := by
  have hf : RespectsAt (emptyPresented I) rfl
      (zeroRawLeafLabel I (emptyPresented I).domain) := by
    intro e he
    have hempty : e ∉ (∅ : Finset I.RowId) := by simp
    exact (hempty he).elim
  exact existsUnique_compatibleTransport
    (emptyPresented I) (emptyPresented I) (empty_rel I)
      (zeroRawLeafLabel I (emptyPresented I).domain) hf

end
end PvNP.RealizableHardness.ActualLeafTransportChecks
