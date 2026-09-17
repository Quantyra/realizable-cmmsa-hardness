import PvNP.RealizableHardness.ActualLeafRejectionUnion

namespace PvNP.RealizableHardness.ActualLeafRejectionUnionChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open scoped BigOperators
noncomputable section

#check restrictionAgreesOnCenter
#check restrictionAgreesOnCenter_iff_source
#check leafFailIndicator
#check leafFailIndicator_nonneg
#check leafFailIndicator_le_one
#check anyFailIndicator
#check anyFailIndicator_le_sum
#check anyFailIndicator_le_card

#print axioms restrictionAgreesOnCenter_iff_source
#print axioms leafFailIndicator_nonneg
#print axioms leafFailIndicator_le_one
#print axioms anyFailIndicator_le_sum
#print axioms anyFailIndicator_le_card

local instance representativeSamplerChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

/-! Three distinct actual original-row questions, with the zero-dimensional
center `K = ⊥`, exercise the relation class and center invariance. -/

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

theorem source_vertex_rel : LeafVertex.Rel sourceVertex sourceVertex :=
  LeafVertex.Rel.refl sourceVertex

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

theorem source_center_eq : sourceCenter.K = sourceCenter.K :=
  rfl

def midPackaged : LeafLabel midVertex :=
  transportedLeafLabel source_mid_vertex_rel sourcePackaged

example :
    restrictionAgreesOnCenter source_vertex_rel sourceCenter sourceCenter
      source_center_eq sourcePackaged sourcePackaged ↔
      LinearMap.comp (restrictToCenter sourceCenter sourcePackaged)
          (Submodule.inclusion (le_of_eq source_center_eq.symm)) =
        restrictToCenter sourceCenter sourcePackaged :=
  restrictionAgreesOnCenter_iff_source source_vertex_rel sourceCenter sourceCenter
    source_center_eq sourcePackaged sourcePackaged

example :
    restrictionAgreesOnCenter source_mid_vertex_rel sourceCenter midCenter
      source_mid_center_eq sourcePackaged midPackaged ↔
      LinearMap.comp (restrictToCenter sourceCenter sourcePackaged)
          (Submodule.inclusion (le_of_eq source_mid_center_eq.symm)) =
        restrictToCenter midCenter midPackaged :=
  restrictionAgreesOnCenter_iff_source source_mid_vertex_rel sourceCenter midCenter
    source_mid_center_eq sourcePackaged midPackaged

example :
    anyFailIndicator
      (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
      (fun _ => source_vertex_rel)
      (fun _ => sourceCenter) (fun _ => sourceCenter)
      (fun _ => source_center_eq)
      (fun _ => sourcePackaged) (fun _ => sourcePackaged) ≤
      ∑ _i : Fin 1,
        leafFailIndicator source_vertex_rel sourceCenter sourceCenter
          source_center_eq sourcePackaged sourcePackaged :=
  anyFailIndicator_le_sum
    (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
    (fun _ => source_vertex_rel)
    (fun _ => sourceCenter) (fun _ => sourceCenter)
    (fun _ => source_center_eq)
    (fun _ => sourcePackaged) (fun _ => sourcePackaged)

example :
    anyFailIndicator
      (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
      (fun _ => source_vertex_rel)
      (fun _ => sourceCenter) (fun _ => sourceCenter)
      (fun _ => source_center_eq)
      (fun _ => sourcePackaged) (fun _ => sourcePackaged) ≤ ((1 : Nat) : ℝ) :=
  anyFailIndicator_le_card
    (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
    (fun _ => source_vertex_rel)
    (fun _ => sourceCenter) (fun _ => sourceCenter)
    (fun _ => source_center_eq)
    (fun _ => sourcePackaged) (fun _ => sourcePackaged)

example :
    anyFailIndicator
      (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => midVertex)
      (fun _ => source_mid_vertex_rel)
      (fun _ => sourceCenter) (fun _ => midCenter)
      (fun _ => source_mid_center_eq)
      (fun _ => sourcePackaged) (fun _ => midPackaged) ≤
      ∑ _i : Fin 1,
        leafFailIndicator source_mid_vertex_rel sourceCenter midCenter
          source_mid_center_eq sourcePackaged midPackaged :=
  anyFailIndicator_le_sum
    (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => midVertex)
    (fun _ => source_mid_vertex_rel)
    (fun _ => sourceCenter) (fun _ => midCenter)
    (fun _ => source_mid_center_eq)
    (fun _ => sourcePackaged) (fun _ => midPackaged)

example :
    anyFailIndicator
      (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
      (fun _ => source_mid_vertex_rel)
      (fun _ => sourceCenter) (fun _ => midCenter)
      (fun _ => source_mid_center_eq)
      (fun _ => sourcePackaged) (fun _ => midPackaged) ≤
      ∑ _i : Fin 2,
        leafFailIndicator source_mid_vertex_rel sourceCenter midCenter
          source_mid_center_eq sourcePackaged midPackaged :=
  anyFailIndicator_le_sum
    (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
    (fun _ => source_mid_vertex_rel)
    (fun _ => sourceCenter) (fun _ => midCenter)
    (fun _ => source_mid_center_eq)
    (fun _ => sourcePackaged) (fun _ => midPackaged)

example :
    anyFailIndicator
      (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
      (fun _ => source_mid_vertex_rel)
      (fun _ => sourceCenter) (fun _ => midCenter)
      (fun _ => source_mid_center_eq)
      (fun _ => sourcePackaged) (fun _ => midPackaged) ≤ ((2 : Nat) : ℝ) :=
  anyFailIndicator_le_card
    (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
    (fun _ => source_mid_vertex_rel)
    (fun _ => sourceCenter) (fun _ => midCenter)
    (fun _ => source_mid_center_eq)
    (fun _ => sourcePackaged) (fun _ => midPackaged)

/-! The empty boundary exercises the same class membership and k = 0 center. -/

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
    restrictionAgreesOnCenter (empty_vertex_rel I) (emptyCenter I) (emptyCenter I)
      (empty_center_eq I) (emptyPackaged I) (emptyPackaged I) ↔
      LinearMap.comp (restrictToCenter (emptyCenter I) (emptyPackaged I))
          (Submodule.inclusion (le_of_eq (empty_center_eq I).symm)) =
        restrictToCenter (emptyCenter I) (emptyPackaged I) :=
  restrictionAgreesOnCenter_iff_source (empty_vertex_rel I) (emptyCenter I)
    (emptyCenter I) (empty_center_eq I) (emptyPackaged I) (emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    anyFailIndicator
      (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) ≤
      ∑ _i : Fin 0,
        leafFailIndicator (empty_vertex_rel I) (emptyCenter I) (emptyCenter I)
          (empty_center_eq I) (emptyPackaged I) (emptyPackaged I) :=
  anyFailIndicator_le_sum
    (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    anyFailIndicator
      (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) ≤ ((0 : Nat) : ℝ) :=
  anyFailIndicator_le_card
    (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    anyFailIndicator
      (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) ≤
      ∑ _i : Fin 1,
        leafFailIndicator (empty_vertex_rel I) (emptyCenter I) (emptyCenter I)
          (empty_center_eq I) (emptyPackaged I) (emptyPackaged I) :=
  anyFailIndicator_le_sum
    (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    anyFailIndicator
      (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) ≤ ((1 : Nat) : ℝ) :=
  anyFailIndicator_le_card
    (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)

end
end PvNP.RealizableHardness.ActualLeafRejectionUnionChecks
