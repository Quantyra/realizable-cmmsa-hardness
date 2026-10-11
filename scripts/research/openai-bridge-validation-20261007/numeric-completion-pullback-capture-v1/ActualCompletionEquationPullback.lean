import PvNP.RealizableHardness.ActualVisibleQuestionCompletion
import PvNP.RealizableHardness.ActualRhsFunctionalConstruction
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! Actual completion equation spaces in the original row-coordinate frame.
The frame is used only to identify events in the existing sampling law. -/
namespace PvNP.RealizableHardness.ActualCompletionEquationPullback

open PvNP.RealizableHardness
open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualTaggedFixedCenterGeometry ActualTaggedConcreteStarLaw
open ActualTaggedRowDeletion ActualVisibleQuestionCompletion ActualRhsFunctionalConstruction
open TripleRestrictionRank

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _

/-- The fixed original row frame embedded into actual global variables. -/
def coordinateGlobalMap : Vector J →ₗ[ZMod 2] TaggedAmbient I copies :=
  (ActualCoordinateSpace I copies U).subtype.comp
    (actualRowCoordinateEquiv I copies U).symm.toLinearMap

theorem coordinateGlobalMap_injective :
    Function.Injective (coordinateGlobalMap I copies U) :=
  (ActualCoordinateSpace I copies U).injective_subtype.comp
    (actualRowCoordinateEquiv I copies U).symm.injective

def visibleSetForDraw (d : Draw J) : Finset (TaggedVar I copies) :=
  retainedVariables I copies J U ((rowDrawEquiv I copies U).symm d)

def completionForDraw (d : Draw J) : TaggedGoodU I copies J :=
  completion I copies J (visibleSetForDraw I copies U d)
    (retainedVariables_reachable I copies J U ((rowDrawEquiv I copies U).symm d))

theorem completionForDraw_eq_of_visible_eq (d e : Draw J)
    (heq : visibleSetForDraw I copies U d = visibleSetForDraw I copies U e) :
    completionForDraw I copies U d = completionForDraw I copies U e :=
  completion_eq_of_visible_eq I copies J _ _ _ _ heq

def completionEquationSpace (d : Draw J) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  equationSpan (taggedSource I copies).support (completionForDraw I copies U d).1

def completionPulledBack (d : Draw J) : Submodule (ZMod 2) (Vector J) :=
  (completionEquationSpace I copies U d).comap (coordinateGlobalMap I copies U)

theorem completionEquationSpace_finrank (d : Draw J) :
    Module.finrank (ZMod 2) (completionEquationSpace I copies U d) = J := by
  unfold completionEquationSpace
  rw [equationSpan_finrank_eq_card (taggedSource I copies).support
    (taggedSource I copies).support_card _ (completionForDraw I copies U d).2.1]
  exact (completionForDraw I copies U d).2.2

/-- No dimension-J premise for the chosen completion is assumed. -/
theorem completionPulledBack_finrank_le (d : Draw J) :
    Module.finrank (ZMod 2) (completionPulledBack I copies U d) ≤ J := by
  letI : Module.Finite (ZMod 2) (TaggedAmbient I copies) := Module.Finite.of_finite
  let f : completionPulledBack I copies U d →ₗ[ZMod 2]
      completionEquationSpace I copies U d :=
    ((coordinateGlobalMap I copies U).comp
      (completionPulledBack I copies U d).subtype).codRestrict
        (completionEquationSpace I copies U d) (fun x => x.2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply coordinateGlobalMap_injective I copies U
    exact congrArg Subtype.val hxy
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  rw [completionEquationSpace_finrank I copies U d] at hdim
  exact hdim

/-- Every concrete retained vector has the same visible global support
under the fixed frame, including all deletion outcomes. -/
theorem retained_map_global_eq_visible (d : Draw J) :
    (retained d).map (coordinateGlobalMap I copies U) =
      visibleCoordinateSpace I copies (visibleSetForDraw I copies U d) := by
  let s := (rowDrawEquiv I copies U).symm d
  have hdraw : rowDrawEquiv I copies U s = d := (rowDrawEquiv I copies U).apply_symm_apply d
  have hcoords := actualRetained_map_coordinates I copies U s
  rw [hdraw] at hcoords
  have hcomp : (coordinateGlobalMap I copies U).comp
      (actualRowCoordinateEquiv I copies U).toLinearMap =
        (ActualCoordinateSpace I copies U).subtype := by
    ext x
    change ((actualRowCoordinateEquiv I copies U).symm
      (actualRowCoordinateEquiv I copies U x)).1 = x.1
    rw [LinearEquiv.symm_apply_apply]
  calc
    (retained d).map (coordinateGlobalMap I copies U) =
        ((actualRetained I copies U s).map
          (actualRowCoordinateEquiv I copies U).toLinearMap).map
            (coordinateGlobalMap I copies U) := by rw [hcoords]
    _ = (actualRetained I copies U s).map (ActualCoordinateSpace I copies U).subtype := by
      rw [Submodule.map_map, hcomp]
    _ = visibleCoordinateSpace I copies (visibleSetForDraw I copies U d) :=
      actualRetained_map_visible I copies J U s

/-- Exact event equality under the original injection. H may be the
completion chosen from the retained question; no independence is used. -/
theorem completion_intersection_eq_bot_iff (d : Draw J)
    (Q : Submodule (ZMod 2) (Vector J)) :
    Q ⊓ completionPulledBack I copies U d = ⊥ ↔
      Q.map (coordinateGlobalMap I copies U) ⊓ completionEquationSpace I copies U d = ⊥ := by
  constructor
  · intro hbot
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy.1
    have hxH : x ∈ completionPulledBack I copies U d := by
      change coordinateGlobalMap I copies U x ∈ completionEquationSpace I copies U d
      simpa only [hxy] using hy.2
    have hx0 : x ∈ (⊥ : Submodule (ZMod 2) (Vector J)) := hbot ▸ ⟨hx, hxH⟩
    have hzero := Submodule.mem_bot.mp hx0
    change y = 0
    rw [← hxy, hzero, map_zero]
  · intro hbot
    apply le_antisymm _ bot_le
    intro x hx
    have hfx : coordinateGlobalMap I copies U x ∈
        Q.map (coordinateGlobalMap I copies U) ⊓ completionEquationSpace I copies U d :=
      ⟨⟨x, hx.1, rfl⟩, hx.2⟩
    have hzero : coordinateGlobalMap I copies U x = 0 :=
      Submodule.mem_bot.mp (hbot ▸ hfx)
    change x = 0
    apply coordinateGlobalMap_injective I copies U
    simpa only [map_zero] using hzero

theorem completion_nontransverse_iff (d : Draw J)
    (Q : Submodule (ZMod 2) (Vector J)) :
    Q ⊓ completionPulledBack I copies U d ≠ ⊥ ↔
      Q.map (coordinateGlobalMap I copies U) ⊓ completionEquationSpace I copies U d ≠ ⊥ :=
  not_congr (completion_intersection_eq_bot_iff I copies U d Q)

theorem retained_advice_global_le_visible (d : Draw J)
    (Q : Submodule (ZMod 2) (Vector J)) (hQ : Q ≤ retained d) :
    Q.map (coordinateGlobalMap I copies U) ≤
      visibleCoordinateSpace I copies (visibleSetForDraw I copies U d) := by
  rw [← retained_map_global_eq_visible I copies U d]
  exact Submodule.map_mono hQ

end
end PvNP.RealizableHardness.ActualCompletionEquationPullback
