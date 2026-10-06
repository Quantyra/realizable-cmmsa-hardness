import PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
import PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
import PvNP.RealizableHardness.ActualStarJointKernel

/-! Internal event transport from the fixed-center coordinate-extension
carrier to the actual `DomainDraw` carrier.  This does not identify either
carrier's law with a physical transverse-leaf/source sampling law. -/

namespace PvNP.RealizableHardness.ActualStarDomainDrawEventBridge

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarJointKernel
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m J t : Nat}
variable {I : PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance N m}

/-- The span of the full ordered family of quotient leaves associated with
one actual tuple of domain draws.  The ambient is the actual `CenterQuotient`.
-/
def domainDrawJointImage (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (draws : Fin m → DomainDraw center h) :
    Submodule (ZMod 2) (CenterQuotient center) :=
  ⨆ i : Fin m, (domainDrawEquiv center h ht hh (draws i)).val

private theorem grassCast_val {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {a b : Nat}
    (h : a = b) (L : Grass V a) :
    (cast (congrArg (Grass V) h) L).val = L.val := by
  cases h
  rfl

/-- The exact leafwise comparison used to identify the two quotient carriers.
The cast only reconciles `(J+2h)-(J+t)` with `2h-t`. -/
theorem domainDrawExtension_quotient_eq
    (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) (D : DomainDraw center h) :
    (upperQuotientEquiv (coordinateCenterGrass center) (by omega)
      (domainDrawExtensionEquiv center h ht hh D)).val =
      (domainDrawEquiv center h ht hh D).val := by
  let U := coordinateCenterGrass center
  have had : J + t ≤ J + 2*h := by omega
  have hdim : 2*h - t = (J + 2*h) - (J + t) := by omega
  have hRank : Grass (CenterQuotient center) (2*h - t) =
      Grass (questionCoordinateSpace center ⧸ U.val)
        ((J + 2*h) - (J + t)) := by
    simp only [CenterQuotient, U, coordinateCenterGrass]
    exact congrArg (Grass (questionCoordinateSpace center ⧸ U.val)) hdim
  have hcastVal :
      (cast hRank
        (domainDrawEquiv center h ht hh D)).val =
        (domainDrawEquiv center h ht hh D).val := by
    have hproof : hRank = congrArg
        (Grass (questionCoordinateSpace center ⧸ U.val)) hdim :=
      Subsingleton.elim _ _
    rw [hproof]
    exact grassCast_val hdim _
  simpa [U, hRank, domainDrawExtensionEquiv, Equiv.trans_apply] using hcastVal

/-- Preimage membership of the full B27 fixed-center bad event is exactly a
rank defect of the joint image of all quotient leaves in `CenterQuotient`.
The tuple arity is the same `m` as the jointly-direct predicate; no pairwise
replacement is made. -/
theorem fixedCenterBad_preimage_iff_domainDraw_rankFailure
    (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    [Finite (CenterQuotient center)]
    [Fintype (Fin m → DomainDraw center h)]
    (draws : Fin m → DomainDraw center h) :
    draws ∈ preimageEvent
        (domainDrawTupleExtensionEquiv center h m ht hh)
        (fixedCenterBadEvent (V := questionCoordinateSpace center)
          (m := m) (coordinateCenterGrass center)) ↔
      Module.finrank (ZMod 2) (domainDrawJointImage center h ht hh draws) ≠
        m * (2*h - t) := by
  classical
  letI : DecidableEq
      (Fin m → Extension (coordinateCenterGrass center) (J + 2*h)) :=
    Classical.decEq _
  let U := coordinateCenterGrass center
  let leaves := domainDrawTupleExtensionEquiv center h m ht hh draws
  have hspan : jointIncrementSpan
      (⟨coordinateCenterGrass center, leaves⟩ :
        StarTuple (V := questionCoordinateSpace center)
        (J + t) (J + 2*h) m) =
      domainDrawJointImage center h ht hh draws := by
    unfold jointIncrementSpan domainDrawJointImage
    apply iSup_congr
    intro i
    change (upperQuotientEquiv U (by omega)
      (domainDrawExtensionEquiv center h ht hh (draws i))).val = _
    exact domainDrawExtension_quotient_eq center h ht hh (draws i)
  have hdim : (J + 2*h) - (J + t) = 2*h - t := by omega
  have hpre : draws ∈ preimageEvent
      (domainDrawTupleExtensionEquiv center h m ht hh)
      (fixedCenterBadEvent (V := questionCoordinateSpace center)
        (m := m) (coordinateCenterGrass center)) ↔
      leaves ∈ fixedCenterBadEvent (V := questionCoordinateSpace center)
        (m := m) (coordinateCenterGrass center) := by
    rw [preimageEvent, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rfl
  have hbad : leaves ∈ fixedCenterBadEvent
      (V := questionCoordinateSpace center) (m := m)
        (coordinateCenterGrass center) ↔
      Module.finrank (ZMod 2) (domainDrawJointImage center h ht hh draws) ≠
        m * (2*h - t) := by
    change leaves ∈ Finset.univ.filter
      (fun Ls : Fin m → Extension (coordinateCenterGrass center) (J + 2*h) =>
        ¬ jointlyDirect
          (⟨coordinateCenterGrass center, Ls⟩ :
            StarTuple (V := questionCoordinateSpace center)
              (J + t) (J + 2*h) m)) ↔ _
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [jointlyDirect, hspan, hdim]
    rfl
  exact hpre.trans hbad

end
end PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
