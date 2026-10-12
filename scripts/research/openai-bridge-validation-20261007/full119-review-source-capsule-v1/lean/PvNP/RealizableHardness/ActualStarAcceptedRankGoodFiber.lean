import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForceSelection
import PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Provisional actual-leaf bridge for the fixed-center DomainDraw law.
This module does not identify this law with the manuscript physical sampler,
and makes no positive acceptance-mass or pre-draw-selection claim. -/

namespace PvNP.RealizableHardness.ActualStarAcceptedRankGoodFiber

open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForceSelection
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N nRows r J t h : Nat}
variable {I : ActualOccurrenceAllocation.Instance N nRows}

/-- The single, named inclusion from the fixed equation span into the
DomainDraw carrier. Naming this map makes the source-side proof term shared
literally by the theorem statement and its proof. -/
def drawEquationInclusion
    (center : QuestionCenter I J t) (D : DomainDraw center h) :
    equationSpan I.support center.U →ₗ[ZMod 2] D.1 :=
  Submodule.inclusion
    (drawPresentation_domain center h D ▸
      PresentedLeaf.H_le_domain (drawPresentation center h D))

/-- The actual table label on a fixed DomainDraw satisfies the prescribed
row equations on the center's equation span.  This uses the LeafLabel source
contract and transports its witness to the canonical draw presentation. -/
theorem drawTableLabel_agrees_rhs
    (center : QuestionCenter I J t) (D : DomainDraw center h)
    (T : ActualCliqueCollisionTransfer.LeafTable I J h) :
    (T (drawVertex center h D)).1.comp (drawEquationInclusion center D) =
      Classical.choose (actual_existsUnique_rhsFunctional I center.U center.goodU) := by
  classical
  let P := Classical.choose (T (drawVertex center h D)).2
  let hP := Classical.choose (Classical.choose_spec (T (drawVertex center h D)).2)
  let hD' := hP.trans (drawVertex_val center h D)
  have hQ : (drawPresentation center h D).domain = D.1 :=
    drawPresentation_domain center h D
  have hfP : RespectsAt P hP (T (drawVertex center h D)).1 :=
    Classical.choose_spec (Classical.choose_spec (T (drawVertex center h D)).2)
  have hfQ : RespectsAt (drawPresentation center h D) hQ
      (T (drawVertex center h D)).1 :=
    (respectsAt_iff_of_domain_eq P (drawPresentation center h D) hD' hQ
      (T (drawVertex center h D)).1).mp hfP
  let l := (T (drawVertex center h D)).1.comp (drawEquationInclusion center D)
  have hψ := Classical.choose_spec (actual_existsUnique_rhsFunctional I center.U center.goodU)
  have hlrows : ∀ e (he : e ∈ center.U),
      l ⟨equationVector I.support e,
        equationVector_mem_equationSpan I.support center.U e he⟩ = I.rowRhs e := by
    intro e he
    have hx := hfQ e he
    change (T (drawVertex center h D)).1.toFun ⟨equationVector I.support e,
      hQ ▸ PresentedLeaf.H_le_domain (drawPresentation center h D)
        (equationVector_mem_equationSpan I.support center.U e he)⟩ = I.rowRhs e at hx
    change (T (drawVertex center h D)).1.toFun (drawEquationInclusion center D
      ⟨equationVector I.support e,
        equationVector_mem_equationSpan I.support center.U e he⟩) = I.rowRhs e
    have harg : drawEquationInclusion center D
        ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support center.U e he⟩ =
        ⟨equationVector I.support e,
          hQ ▸ PresentedLeaf.H_le_domain (drawPresentation center h D)
            (equationVector_mem_equationSpan I.support center.U e he)⟩ := by
      apply Subtype.ext
      rfl
    rw [harg]
    exact hx
  have huniq := hψ.2 l hlrows
  simpa only [l] using huniq

/-- The image of a DomainDraw's coordinate carrier in the fixed-center
quotient is exactly the B50ap quotient leaf. This is the carrier identity
needed to descend table-minus-base labels without substituting a lookalike
range. -/
theorem domainDraw_restrictedQuotient_eq
    (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) (D : DomainDraw center h) :
    (D.1.comap (questionCoordinateSpace center).subtype).map
        (centerSpanInCoordinate center).mkQ =
      (domainDrawEquiv center h ht hh D).val := by
  classical
  simpa using (domainDrawEquiv_val center h ht hh D).symm

/-- Rewriting the restriction map's range exposes the exact B50ap carrier. -/
theorem domainDraw_restrictedRange_eq
    (center : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) (D : DomainDraw center h) :
    LinearMap.range
        ((centerSpanInCoordinate center).mkQ.domRestrict
          (D.1.comap (questionCoordinateSpace center).subtype)) =
      (domainDrawEquiv center h ht hh D).val := by
  rw [LinearMap.range_domRestrict]
  exact domainDraw_restrictedQuotient_eq center h ht hh D

end
end PvNP.RealizableHardness.ActualStarAcceptedRankGoodFiber
