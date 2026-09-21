import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw

namespace PvNP.RealizableHardness.ActualQuestionCenterDomainDrawChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualStarSpanIntersection

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

local instance checksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

#check QuestionCenter
#check Ambient
#check questionEquationSpan
#check questionCoordinateSpace
#check centerEquationSpan
#check centerSpanInCoordinate
#check CenterQuotient
#check DomainDraw
#check domainDrawFinite
#check domainDrawFintype
#check coordinateSpaceLinearEquiv
#check questionSupport_card
#check coordinateSpace_finrank
#check equationSpan_finrank
#check centerEquationSpan_le_coordinateSpace
#check centerEquationSpan_finrank
#check centerSpanInCoordinate_finrank
#check centerQuotient_finrank
#check domainDrawEquiv
#check domainDraw_card
#check domainDraw_nonempty
#check drawPresentation
#check drawPresentation_domain
#check drawPresentation_center_le
#check drawVertex
#check drawVertex_val
#check drawCenter
#check drawVertex_rel_iff
#check drawVertex_injective
#check cliqueOf_drawVertex_eq_iff
#check cliqueOf_drawVertex_injective

#print axioms questionSupport_card
#print axioms coordinateSpace_finrank
#print axioms equationSpan_finrank
#print axioms centerEquationSpan_finrank
#print axioms centerQuotient_finrank
#print axioms domainDraw_card
#print axioms domainDraw_nonempty
#print axioms drawPresentation_domain
#print axioms drawVertex_rel_iff
#print axioms cliqueOf_drawVertex_eq_iff

example {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) (D : DomainDraw q h) :
    (domainDrawEquiv q h ht hh).symm ((domainDrawEquiv q h ht hh) D) = D :=
  (domainDrawEquiv q h ht hh).symm_apply_apply D

example {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (G : Grass (CenterQuotient q) (2*h - t)) :
    (domainDrawEquiv q h ht hh) ((domainDrawEquiv q h ht hh).symm G) = G :=
  (domainDrawEquiv q h ht hh).apply_symm_apply G

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    QuestionCenter I 0 0 :=
  { U := ∅
    goodU := by simp [GoodQuestion]
    card_U := by simp
    K := ⊥
    K_le := by simp
    finrank_K := by simp
    transverse := by simp [questionEquationSpan] }

def emptyQuestionCenter {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    QuestionCenter I 0 0 :=
  { U := ∅
    goodU := by simp [GoodQuestion]
    card_U := by simp
    K := ⊥
    K_le := by simp
    finrank_K := by simp
    transverse := by simp [questionEquationSpan] }

def emptyDomainDraw {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    DomainDraw (emptyQuestionCenter I) 0 :=
  { val := ⊥
    property := by
      simp [questionEquationSpan, equationSpan, emptyQuestionCenter,
        Submodule.span_empty] }

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    Fintype.card (DomainDraw (emptyQuestionCenter I) 0) = 1 := by
  have h := domainDraw_card (emptyQuestionCenter I) 0 (by simp) (by simp)
  simpa only [emptyQuestionCenter, Nat.mul_zero, Nat.zero_sub,
    GrassmannCounting.gaussian_zero] using h

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    (drawPresentation (emptyQuestionCenter I) 0 (emptyDomainDraw I)).domain =
      (emptyDomainDraw I).1 :=
  drawPresentation_domain (emptyQuestionCenter I) 0 (emptyDomainDraw I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    (drawVertex (emptyQuestionCenter I) 0 (emptyDomainDraw I)).1 =
      (emptyDomainDraw I).1 :=
  drawVertex_val (emptyQuestionCenter I) 0 (emptyDomainDraw I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    CenterSubspace (drawVertex (emptyQuestionCenter I) 0 (emptyDomainDraw I)) 0 :=
  drawCenter (emptyQuestionCenter I) 0 (emptyDomainDraw I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    LeafVertex.Rel
        (drawVertex (emptyQuestionCenter I) 0 (emptyDomainDraw I))
        (drawVertex (emptyQuestionCenter I) 0 (emptyDomainDraw I)) := by
  exact (drawVertex_rel_iff (emptyQuestionCenter I) 0
    (emptyDomainDraw I) (emptyDomainDraw I)).mpr rfl

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    cliqueOf (drawVertex (emptyQuestionCenter I) 0 (emptyDomainDraw I)) =
      cliqueOf (drawVertex (emptyQuestionCenter I) 0 (emptyDomainDraw I)) := by
  exact (cliqueOf_drawVertex_eq_iff (emptyQuestionCenter I) 0
    (emptyDomainDraw I) (emptyDomainDraw I)).mpr rfl

end
end PvNP.RealizableHardness.ActualQuestionCenterDomainDrawChecks
