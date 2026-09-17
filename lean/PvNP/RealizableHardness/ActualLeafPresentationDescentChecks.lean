import PvNP.RealizableHardness.ActualLeafPresentationDescent

namespace PvNP.RealizableHardness.ActualLeafPresentationDescentChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section

#check vertexH
#check vertexH_eq_of_presentation
#check LeafVertex.Rel
#check LeafVertex.Rel_iff_presented
#check LeafVertex.Rel.refl
#check LeafVertex.Rel.symm
#check LeafVertex.Rel.trans
#check packagedLabel
#check packagedLabel_toFun
#check LeafLabel.eq_of_toFun
#check transportedLeafLabel
#check transportedLeafLabel_agrees_presented
#check transportedLeafLabel_coherence
#check repeated_address_rowRhs

#print axioms vertexH_eq_of_presentation
#print axioms LeafVertex.Rel_iff_presented
#print axioms LeafVertex.Rel.refl
#print axioms LeafVertex.Rel.symm
#print axioms LeafVertex.Rel.trans
#print axioms packagedLabel_toFun
#print axioms LeafLabel.eq_of_toFun
#print axioms transportedLeafLabel_agrees_presented
#print axioms transportedLeafLabel_coherence
#print axioms repeated_address_rowRhs

local instance presentationDescentChecksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

/-! Three distinct actual original-row questions exercise packaged descent and
sequential versus direct vertex transport with a nonzero source RHS. -/

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

def targetVertex : LeafVertex threeRowActual 1 0 :=
  ⟨(originalPresented 2).domain, ⟨originalPresented 2, rfl⟩⟩

def sourcePackaged : LeafLabel sourceVertex :=
  packagedLabel (originalPresented 0) sourceLabel sourceLabel_respects

theorem source_mid_vertex_rel : LeafVertex.Rel sourceVertex midVertex :=
  (LeafVertex.Rel_iff_presented sourceVertex midVertex
    (originalPresented 0) (originalPresented 1) rfl rfl).mpr (original_rel 0 1)

theorem mid_target_vertex_rel : LeafVertex.Rel midVertex targetVertex :=
  (LeafVertex.Rel_iff_presented midVertex targetVertex
    (originalPresented 1) (originalPresented 2) rfl rfl).mpr (original_rel 1 2)

theorem three_questions_distinct :
    (originalPresented 0).U ≠ (originalPresented 1).U ∧
    (originalPresented 1).U ≠ (originalPresented 2).U ∧
    (originalPresented 0).U ≠ (originalPresented 2).U := by
  simp [originalPresented, originalQuestion]

example : vertexH sourceVertex = (originalPresented 0).H :=
  vertexH_eq_of_presentation sourceVertex (originalPresented 0) rfl

example : sourcePackaged.1 = sourceLabel :=
  packagedLabel_toFun (originalPresented 0) sourceLabel sourceLabel_respects

example :
    (transportedLeafLabel source_mid_vertex_rel sourcePackaged).1 =
      transportedLabel (originalPresented 0) (originalPresented 1)
        (original_rel 0 1) sourceLabel sourceLabel_respects :=
  transportedLeafLabel_agrees_presented (originalPresented 0)
    (originalPresented 1) (original_rel 0 1) sourceLabel sourceLabel_respects

example :
    transportedLeafLabel mid_target_vertex_rel
        (transportedLeafLabel source_mid_vertex_rel sourcePackaged) =
      transportedLeafLabel
        (LeafVertex.Rel.trans source_mid_vertex_rel mid_target_vertex_rel)
        sourcePackaged :=
  transportedLeafLabel_coherence source_mid_vertex_rel mid_target_vertex_rel
    sourcePackaged

example : LeafVertex.Rel sourceVertex sourceVertex :=
  LeafVertex.Rel.refl sourceVertex

example : LeafVertex.Rel midVertex sourceVertex :=
  LeafVertex.Rel.symm source_mid_vertex_rel

example : LeafVertex.Rel sourceVertex targetVertex :=
  LeafVertex.Rel.trans source_mid_vertex_rel mid_target_vertex_rel

/-! Distinct original questions are disjoint, so the shared-address theorem is
exercised on a presentation against itself. Distinct presentations still run
descent and coherence above. -/

theorem row0_mem_source :
    Sum.inl 0 ∈ (originalPresented 0).U := by
  simp [originalPresented, originalQuestion]

example :
    (transportedLabel (originalPresented 0) (originalPresented 0)
        (original_rel 0 0) sourceLabel sourceLabel_respects).toFun
      ⟨equationVector threeRowActual.support (Sum.inl 0),
        (originalPresented 0).H_le_domain
          (equationVector_mem_equationSpan threeRowActual.support
            (originalPresented 0).U (Sum.inl 0) row0_mem_source)⟩ =
      threeRowActual.rowRhs (Sum.inl 0) :=
  repeated_address_rowRhs (originalPresented 0) (originalPresented 0)
    (original_rel 0 0) sourceLabel sourceLabel_respects (Sum.inl 0)
    row0_mem_source row0_mem_source

/-! The empty boundary exercises identity, coherence, and repeated-address on
the zero carrier. -/

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

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    (transportedLeafLabel (empty_vertex_rel I) (emptyPackaged I)).1 =
      transportedLabel (emptyPresented I) (emptyPresented I)
        (PresentedLeaf.Rel.refl (emptyPresented I))
        (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I) :=
  transportedLeafLabel_agrees_presented (emptyPresented I) (emptyPresented I)
    (PresentedLeaf.Rel.refl (emptyPresented I))
    (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    transportedLeafLabel (empty_vertex_rel I)
        (transportedLeafLabel (empty_vertex_rel I) (emptyPackaged I)) =
      transportedLeafLabel
        (LeafVertex.Rel.trans (empty_vertex_rel I) (empty_vertex_rel I))
        (emptyPackaged I) :=
  transportedLeafLabel_coherence (empty_vertex_rel I) (empty_vertex_rel I)
    (emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    transportedLeafLabel (empty_vertex_rel I) (emptyPackaged I) =
      emptyPackaged I := by
  apply LeafLabel.eq_of_toFun
  have hagree := transportedLeafLabel_agrees_presented (emptyPresented I)
    (emptyPresented I) (PresentedLeaf.Rel.refl (emptyPresented I))
    (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)
  exact hagree.trans
    (transportedLabel_identity_canonical (emptyPresented I)
      (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I))

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (e : I.RowId)
    (heP : e ∈ (emptyPresented I).U)
    (heQ : e ∈ (emptyPresented I).U) :
    (transportedLabel (emptyPresented I) (emptyPresented I)
        (PresentedLeaf.Rel.refl (emptyPresented I))
        (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I)).toFun
      ⟨equationVector I.support e,
        (emptyPresented I).H_le_domain
          (equationVector_mem_equationSpan I.support (emptyPresented I).U e heQ)⟩ =
      I.rowRhs e :=
  repeated_address_rowRhs (emptyPresented I) (emptyPresented I)
    (PresentedLeaf.Rel.refl (emptyPresented I))
    (zeroRawLeafLabel I) (zeroRawLeafLabel_respects I) e heP heQ

end
end PvNP.RealizableHardness.ActualLeafPresentationDescentChecks
