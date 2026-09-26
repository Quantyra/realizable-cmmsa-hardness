import PvNP.RealizableHardness.ActualStarDomainDrawEventBridge

/-! The B48 full-joint event bridge with independent source-row count and
ordered tuple arity.  The fixed center remains attached to the source
instance; only the tuple index is `r`. -/

namespace PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarJointKernel
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
open PvNP.RealizableHardness.GrassmannFlagPosterior

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N nRows J t r : Nat}
variable {I : ActualOccurrenceAllocation.Instance N nRows}

/-- The full joint image of an ordered `r`-tuple of actual domain draws in
the quotient by one fixed source-indexed center. -/
def domainDrawJointImageArity
    (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (draws : Fin r → DomainDraw center h) :
    Submodule (ZMod 2) (CenterQuotient center) :=
  ⨆ i : Fin r, (domainDrawEquiv center h ht hh (draws i)).val

/-- Pulling back the B27 bad event along the ordered extension-tuple
equivalence is precisely failure of the full joint rank condition for the
`r`-tuple of quotient leaves. -/
theorem fixedCenterBad_preimage_iff_domainDraw_rankFailure_arity
    (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    [Finite (CenterQuotient center)]
    [Fintype (Fin r → DomainDraw center h)]
    (draws : Fin r → DomainDraw center h) :
    draws ∈ preimageEvent
        (domainDrawTupleExtensionEquiv center h r ht hh)
        (fixedCenterBadEvent (V := questionCoordinateSpace center)
          (m := r) (coordinateCenterGrass center)) ↔
      Module.finrank (ZMod 2)
        (domainDrawJointImageArity center h ht hh draws) ≠
        r * (2*h - t) := by
  classical
  letI : DecidableEq
      (Fin r → Extension (coordinateCenterGrass center) (J + 2*h)) :=
    Classical.decEq _
  let U := coordinateCenterGrass center
  let leaves := domainDrawTupleExtensionEquiv center h r ht hh draws
  have hspan : jointIncrementSpan
      (⟨coordinateCenterGrass center, leaves⟩ :
        StarTuple (V := questionCoordinateSpace center)
        (J + t) (J + 2*h) r) =
      domainDrawJointImageArity center h ht hh draws := by
    unfold jointIncrementSpan domainDrawJointImageArity
    apply iSup_congr
    intro i
    change (upperQuotientEquiv U (by omega)
      (domainDrawExtensionEquiv center h ht hh (draws i))).val = _
    exact domainDrawExtension_quotient_eq center h ht hh (draws i)
  have hdim : (J + 2*h) - (J + t) = 2*h - t := by omega
  have hpre : draws ∈ preimageEvent
      (domainDrawTupleExtensionEquiv center h r ht hh)
      (fixedCenterBadEvent (V := questionCoordinateSpace center)
        (m := r) (coordinateCenterGrass center)) ↔
      leaves ∈ fixedCenterBadEvent (V := questionCoordinateSpace center)
        (m := r) (coordinateCenterGrass center) := by
    rw [preimageEvent, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rfl
  have hbad : leaves ∈ fixedCenterBadEvent
      (V := questionCoordinateSpace center) (m := r)
        (coordinateCenterGrass center) ↔
      Module.finrank (ZMod 2)
        (domainDrawJointImageArity center h ht hh draws) ≠
        r * (2*h - t) := by
    change leaves ∈ Finset.univ.filter
      (fun Ls : Fin r → Extension (coordinateCenterGrass center) (J + 2*h) =>
        ¬ jointlyDirect
          (⟨coordinateCenterGrass center, Ls⟩ :
            StarTuple (V := questionCoordinateSpace center)
              (J + t) (J + 2*h) r)) ↔ _
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [jointlyDirect, hspan, hdim]
    rfl
  exact hpre.trans hbad

end
end PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge
