import PvNP.RealizableHardness.ActualStarAffineFunctionalSelection
import PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
import PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
import PvNP.RealizableHardness.ActualStarJointKernel
import PvNP.RealizableHardness.ActualSourceStarLaw
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Provisional B50 force module.  This file connects the affine-functional
fibre helpers to the actual fixed-center ordered DomainDraw carrier.  It does
not identify that uniform carrier with the manuscript physical sampler. -/

namespace PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForce

open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
open PvNP.RealizableHardness.ActualStarJointKernel
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.GrassmannFlagPosterior

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m J t h : Nat}
variable {I : PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance N m}

/-- For a fixed-center ordered DomainDraw tuple, the rank-good event is
equivalent to injectivity of the canonical map from the direct sum of all
quotient leaves.  This is the whole family, not a pairwise test. -/
theorem domainDraw_rankGood_iff_incrementMap_injective
    (center : QuestionCenter I J t) (ht : t ≤ 2*h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    (draws : Fin m → DomainDraw center h) :
    let U := coordinateCenterGrass center
    let leaves : Fin m → Extension U (J + 2*h) :=
      domainDrawTupleExtensionEquiv center h m ht hh draws
    let z : StarTuple (V := questionCoordinateSpace center)
        (J+t) (J+2*h) m := ⟨U, leaves⟩
    Module.finrank (ZMod 2) (domainDrawJointImage center h ht hh draws) =
        m * (2*h-t) ↔ Function.Injective (incrementSumMap z) := by
  classical
  let U := coordinateCenterGrass center
  let leaves : Fin m → Extension U (J + 2*h) :=
    domainDrawTupleExtensionEquiv center h m ht hh draws
  let z : StarTuple (V := questionCoordinateSpace center)
      (J+t) (J+2*h) m := ⟨U, leaves⟩
  have hspan : jointIncrementSpan z = domainDrawJointImage center h ht hh draws := by
    unfold jointIncrementSpan domainDrawJointImage
    apply iSup_congr
    intro i
    change
      (GrassmannFlagPosterior.upperQuotientEquiv U (by omega)
        (domainDrawExtensionEquiv center h ht hh (draws i))).val =
      (domainDrawEquiv center h ht hh (draws i)).val
    exact domainDrawExtension_quotient_eq center h ht hh (draws i)
  have hdim : (J+2*h) - (J+t) = 2*h-t := by omega
  have hgood : jointlyDirect z ↔
      Module.finrank (ZMod 2) (domainDrawJointImage center h ht hh draws) =
        m * (2*h-t) := by
    change Module.finrank (ZMod 2) (jointIncrementSpan z) =
      m * ((J+2*h)-(J+t)) ↔ _
    rw [hspan, hdim]
    rfl
  have hkernel := jointlyDirect_iff_incrementSumMap_injective
    (V := questionCoordinateSpace center) (t := J+t) (d := J+2*h) z
  constructor
  · intro hgood'
    exact hkernel.mp (hgood.mpr hgood')
  · intro hinj
    exact hgood.mp (hkernel.mpr hinj)

/- Quotient any leaf-table discrepancy that vanishes on the prescribed
center to its actual quotient increment. The range is the explicit carrier. -/
set_option maxHeartbeats 1000000 in
def leafDifferenceOnQuotient
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (S L : Submodule (ZMod 2) V) (hSL : S ≤ L)
    (T : L →ₗ[ZMod 2] ZMod 2) (base : V →ₗ[ZMod 2] ZMod 2)
    (hagree : T.comp (Submodule.inclusion hSL) = base.comp S.subtype) :
    LinearMap.range (S.mkQ.domRestrict L) →ₗ[ZMod 2] ZMod 2 := by
  classical
  let q : L →ₗ[ZMod 2] V ⧸ S := S.mkQ.domRestrict L
  let δ : L →ₗ[ZMod 2] ZMod 2 := T - base.comp L.subtype
  have hker : LinearMap.ker q ≤ LinearMap.ker δ := by
    intro x hx
    have hxq : q x = 0 := LinearMap.mem_ker.mp hx
    have hxS : (x : V) ∈ S := by
      change S.mkQ (x : V) = 0 at hxq
      exact (Submodule.Quotient.mk_eq_zero S (x := (x : V))).mp hxq
    have hT := congrArg (fun F : S →ₗ[ZMod 2] ZMod 2 => F ⟨(x : V), hxS⟩) hagree
    have hxi : Submodule.inclusion hSL ⟨x, hxS⟩ = x := by
      apply Subtype.ext
      rfl
    have hTx : T x = base (x : V) := by
      calc
        T x = T (Submodule.inclusion hSL ⟨x, hxS⟩) := by rw [hxi]
        _ = base (x : V) := hT
    have hzero : δ x = 0 := by
      change T x - base (x : V) = 0
      rw [hTx, sub_self]
    exact LinearMap.mem_ker.mpr hzero
  let e := q.quotKerEquivRange
  let descended := (LinearMap.ker q).liftQ δ hker
  exact descended.comp e.symm.toLinearMap

end
end PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForce
