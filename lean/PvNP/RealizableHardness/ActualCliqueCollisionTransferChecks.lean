import PvNP.RealizableHardness.ActualCliqueCollisionTransfer

namespace PvNP.RealizableHardness.ActualCliqueCollisionTransferChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

local instance checksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

#check LeafTable
#check LeafClique
#check cliqueOf
#check CliqueRepresentative
#check cliqueRepresentativeNonempty
#check RepresentativeChoice
#check representativeChoiceNonempty
#check relClass_eq_iff
#check cliqueOf_eq_iff
#check representative_rel
#check selectedTable
#check selectedTable_clique_consistent

#print axioms relClass_eq_iff
#print axioms cliqueOf_eq_iff
#print axioms representative_rel
#print axioms selectedTable_clique_consistent

/-! The actual three-row source/mid fixture from the sampler checks, copied
without importing any checks module. -/

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

def sourceVertex : LeafVertex threeRowActual 1 0 :=
  ⟨(originalPresented 0).domain, ⟨originalPresented 0, rfl⟩⟩

def midVertex : LeafVertex threeRowActual 1 0 :=
  ⟨(originalPresented 1).domain, ⟨originalPresented 1, rfl⟩⟩

theorem source_mid_vertex_rel : LeafVertex.Rel sourceVertex midVertex :=
  (LeafVertex.Rel_iff_presented sourceVertex midVertex
    (originalPresented 0) (originalPresented 1) rfl rfl).mpr (original_rel 0 1)

example : cliqueOf sourceVertex = cliqueOf midVertex :=
  cliqueOf_eq_iff.mpr source_mid_vertex_rel

example : Nonempty (CliqueRepresentative (cliqueOf sourceVertex)) :=
  inferInstance

example : Nonempty (RepresentativeChoice threeRowActual 1 0) :=
  inferInstance

example (s : RepresentativeChoice threeRowActual 1 0) :
    LeafVertex.Rel (s (cliqueOf sourceVertex)).1 sourceVertex :=
  representative_rel s sourceVertex

example (T : LeafTable threeRowActual 1 0)
    (s : RepresentativeChoice threeRowActual 1 0) :
    transportedLeafLabel source_mid_vertex_rel
        (selectedTable T s sourceVertex) = selectedTable T s midVertex :=
  selectedTable_clique_consistent T s source_mid_vertex_rel

/-! Empty actual-leaf boundary: both the key equality and the selected-table
coherence theorem are invoked on the reflexive actual relation. -/

def emptyPresented {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : PresentedLeaf I 0 0 where
  U := ∅
  goodU := by simp [GoodQuestion]
  card_U := by simp
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

def emptyVertex {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : LeafVertex I 0 0 :=
  ⟨(emptyPresented I).domain, ⟨emptyPresented I, rfl⟩⟩

theorem empty_vertex_rel {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    LeafVertex.Rel (emptyVertex I) (emptyVertex I) :=
  LeafVertex.Rel.refl (emptyVertex I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    cliqueOf (emptyVertex I) = cliqueOf (emptyVertex I) :=
  cliqueOf_eq_iff.mpr (empty_vertex_rel I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (T : LeafTable I 0 0) (s : RepresentativeChoice I 0 0) :
    transportedLeafLabel (empty_vertex_rel I)
        (selectedTable T s (emptyVertex I)) =
      selectedTable T s (emptyVertex I) :=
  selectedTable_clique_consistent T s (empty_vertex_rel I)

end
end PvNP.RealizableHardness.ActualCliqueCollisionTransferChecks
