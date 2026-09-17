import PvNP.RealizableHardness.ActualLeafCenterRestriction

namespace PvNP.RealizableHardness.ActualLeafCenterRestrictionChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section

#check CenterSubspace
#check restrictToCenter
#check restrictToCenter_eq_subtype
#check restrictToCenter_transport

#print axioms restrictToCenter_eq_subtype
#print axioms restrictToCenter_transport

local instance centerRestrictionChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

/-! Three distinct actual original-row questions, with the zero-dimensional
center `K = ⊥`, exercise restriction and transport agreement. -/

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

def sourceVertex : LeafVertex threeRowActual 1 0 :=
  ⟨(originalPresented 0).domain, ⟨originalPresented 0, rfl⟩⟩

def midVertex : LeafVertex threeRowActual 1 0 :=
  ⟨(originalPresented 1).domain, ⟨originalPresented 1, rfl⟩⟩

def sourcePackaged : LeafLabel sourceVertex :=
  packagedLabel (originalPresented 0) sourceLabel sourceLabel_respects

theorem source_mid_vertex_rel : LeafVertex.Rel sourceVertex midVertex :=
  (LeafVertex.Rel_iff_presented sourceVertex midVertex
    (originalPresented 0) (originalPresented 1) rfl rfl).mpr (original_rel 0 1)

def sourceCenter : CenterSubspace sourceVertex 0 where
  K := ⊥
  le_domain := bot_le
  transverse := by simp
  finrank := by simp

def midCenter : CenterSubspace midVertex 0 where
  K := ⊥
  le_domain := bot_le
  transverse := by simp
  finrank := by simp

theorem source_mid_center_eq : sourceCenter.K = midCenter.K :=
  rfl

example :
    restrictToCenter sourceCenter sourcePackaged =
      sourcePackaged.1.comp (Submodule.inclusion sourceCenter.le_domain) :=
  restrictToCenter_eq_subtype sourceCenter sourcePackaged

example :
    restrictToCenter midCenter
        (transportedLeafLabel source_mid_vertex_rel sourcePackaged) =
      LinearMap.comp (restrictToCenter sourceCenter sourcePackaged)
        (Submodule.inclusion (le_of_eq source_mid_center_eq.symm)) :=
  restrictToCenter_transport source_mid_vertex_rel sourceCenter midCenter
    source_mid_center_eq sourcePackaged

/-! The empty boundary exercises the same k = 0 center on the zero carrier. -/

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

def emptyVertex {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : LeafVertex I 0 0 :=
  ⟨(emptyPresented I).domain, ⟨emptyPresented I, rfl⟩⟩

def emptyPackaged {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    LeafLabel (emptyVertex I) :=
  packagedLabel (emptyPresented I) (zeroRawLeafLabel I)
    (zeroRawLeafLabel_respects I)

theorem empty_vertex_rel {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    LeafVertex.Rel (emptyVertex I) (emptyVertex I) :=
  LeafVertex.Rel.refl (emptyVertex I)

def emptyCenter {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    CenterSubspace (emptyVertex I) 0 where
  K := ⊥
  le_domain := bot_le
  transverse := by simp
  finrank := by simp

theorem empty_center_eq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    (emptyCenter I).K = (emptyCenter I).K :=
  rfl

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    restrictToCenter (emptyCenter I) (emptyPackaged I) =
      (emptyPackaged I).1.comp
        (Submodule.inclusion (emptyCenter I).le_domain) :=
  restrictToCenter_eq_subtype (emptyCenter I) (emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    restrictToCenter (emptyCenter I)
        (transportedLeafLabel (empty_vertex_rel I) (emptyPackaged I)) =
      LinearMap.comp (restrictToCenter (emptyCenter I) (emptyPackaged I))
        (Submodule.inclusion (le_of_eq (empty_center_eq I).symm)) :=
  restrictToCenter_transport (empty_vertex_rel I) (emptyCenter I)
    (emptyCenter I) (empty_center_eq I) (emptyPackaged I)

end
end PvNP.RealizableHardness.ActualLeafCenterRestrictionChecks
