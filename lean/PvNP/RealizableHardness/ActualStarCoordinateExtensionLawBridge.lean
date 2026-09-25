import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.ActualStarExtensionProduct
import PvNP.RealizableHardness.GrassmannFlagPosterior

/-! A carrier and uniform-law bridge from fixed question-center domain draws
to the conditional ordered extension law. Events are transported only by
preimage; no source-event correspondence is asserted here.
-/

namespace PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m J t : Nat}
variable {I : PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance N m}

/-- The center subspace in the coordinate ambient, with its actual rank. -/
def coordinateCenterGrass (center : QuestionCenter I J t) :
    Grass (questionCoordinateSpace center) (J + t) :=
  ⟨centerSpanInCoordinate center, by
    simpa [Nat.add_comm] using centerSpanInCoordinate_finrank center⟩

/- Keep the function-space Fintype definitionally aligned with the canonical
   subtype enumeration used by `extensionTupleLaw`. -/
@[reducible] local instance extensionFintype (center : QuestionCenter I J t) (h : Nat)
    [Finite (questionCoordinateSpace center)] :
    Fintype (Extension (coordinateCenterGrass center) (J + 2*h)) :=
  Subtype.fintype fun L : Grass (questionCoordinateSpace center) (J + 2*h) =>
    (coordinateCenterGrass center).val ≤ L.val

/-- One actual domain draw, viewed as an extension of the full center span
`K ⊔ equationSpan`, before passing to the quotient. -/
def domainDrawExtensionEquiv
    (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
    DomainDraw center h ≃
      Extension (coordinateCenterGrass center) (J + 2*h) := by
  let U := coordinateCenterGrass center
  have had : J + t ≤ J + 2*h := by omega
  have hrank : 2*h - t = (J + 2*h) - (J + t) := by omega
  let eQ := domainDrawEquiv center h ht hh
  let eRank : Grass (CenterQuotient center) (2*h - t) ≃
      Grass (questionCoordinateSpace center ⧸ U.val)
        ((J + 2*h) - (J + t)) :=
    Equiv.cast (by
      simp only [CenterQuotient, U, coordinateCenterGrass]
      congr 1)
  exact eQ.trans (eRank.trans (upperQuotientEquiv U had).symm)

/-- Coordinatewise lift of `domainDrawExtensionEquiv` to an ordered tuple.
The index set is arbitrary, including the empty tuple. -/
def domainDrawTupleExtensionEquiv
    (center : QuestionCenter I J t) (h r : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
    (Fin r → DomainDraw center h) ≃
      (Fin r → Extension (coordinateCenterGrass center) (J + 2*h)) where
  toFun draws i := domainDrawExtensionEquiv center h ht hh (draws i)
  invFun leaves i := (domainDrawExtensionEquiv center h ht hh).symm (leaves i)
  left_inv draws := by
    funext i
    exact (domainDrawExtensionEquiv center h ht hh).left_inv (draws i)
  right_inv leaves := by
    funext i
    exact (domainDrawExtensionEquiv center h ht hh).right_inv (leaves i)

/-- Uniform law on the ordered domain-draw tuple, with nonemptiness supplied
by an explicit tuple witness rather than a hidden carrier instance. -/
def uniformDomainTupleLaw
    (center : QuestionCenter I J t) (h r : Nat)
    [Fintype (Fin r → DomainDraw center h)]
    (witness : Fin r → DomainDraw center h) :
    FiniteLaw (Fin r → DomainDraw center h) :=
  @uniformLaw (Fin r → DomainDraw center h) inferInstance ⟨witness⟩

/-- The pushforward of the uniform ordered domain tuple law is the actual
conditional ordered extension-tuple law. The domain witness makes the source
carrier nonempty; the target witness is its image. -/
theorem uniform_domainTuple_pushforward_extensionTupleLaw
    (center : QuestionCenter I J t) (h r : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    [Fintype (Fin r → DomainDraw center h)]
    (witness : Fin r → DomainDraw center h) :
    pushforward (domainDrawTupleExtensionEquiv center h r ht hh)
        (uniformDomainTupleLaw center h r witness) =
      extensionTupleLaw (coordinateCenterGrass center)
        (domainDrawTupleExtensionEquiv center h r ht hh witness) := by
  letI : Nonempty (Fin r → DomainDraw center h) := ⟨witness⟩
  letI : Nonempty
      (Fin r → Extension (coordinateCenterGrass center) (J + 2*h)) :=
    ⟨domainDrawTupleExtensionEquiv center h r ht hh witness⟩
  change pushforward (domainDrawTupleExtensionEquiv center h r ht hh)
      (uniformLaw (Fin r → DomainDraw center h)) =
    uniformLaw (Fin r → Extension (coordinateCenterGrass center) (J + 2*h))
  exact pushforward_uniformLaw_equiv (domainDrawTupleExtensionEquiv center h r ht hh)

/-- Exact event-mass transport for any event on the conditional extension
tuple carrier. Its domain-side event is expressly the preimage; interpreting
that preimage as a separate physical/source bad event requires a later proof.
-/
theorem extensionTuple_eventMass_eq_preimage
    (center : QuestionCenter I J t) (h r : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    [Finite (questionCoordinateSpace center)]
    [Fintype (Fin r → DomainDraw center h)]
    (witness : Fin r → DomainDraw center h)
    (E : Finset (Fin r → Extension (coordinateCenterGrass center) (J + 2*h))) :
    eventMass
        (extensionTupleLaw (coordinateCenterGrass center)
          (domainDrawTupleExtensionEquiv center h r ht hh witness)) E =
      eventMass (uniformDomainTupleLaw center h r witness)
        (preimageEvent (domainDrawTupleExtensionEquiv center h r ht hh) E) := by
  letI : Nonempty (Fin r → DomainDraw center h) := ⟨witness⟩
  letI : Nonempty
      (Fin r → Extension (coordinateCenterGrass center) (J + 2*h)) :=
    ⟨domainDrawTupleExtensionEquiv center h r ht hh witness⟩
  rw [← uniform_domainTuple_pushforward_extensionTupleLaw
    center h r ht hh witness]
  exact eventMass_pushforward (domainDrawTupleExtensionEquiv center h r ht hh)
    (uniformLaw (Fin r → DomainDraw center h)) E

end
end PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
