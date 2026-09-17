import PvNP.RealizableHardness.ActualLeafRejectionUnion
import Mathlib.Basic.Real.Basic

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

/-- The star test accepts when every queried leaf agrees with its source on the shared center. -/
def starAccepts
    {n k : Nat}
    (vs : Fin n → LeafVertex I J h)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel (vs i) (ws i))
    (Cvs : ∀ i, CenterSubspace (vs i) k)
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, (Cvs i).K = (Cws i).K)
    (φvs : ∀ i, LeafLabel (vs i))
    (φws : ∀ i, LeafLabel (ws i)) : Prop :=
  ∀ i, restrictionAgreesOnCenter (hrel i) (Cvs i) (Cws i) (hK i) (φvs i) (φws i)

theorem starAccepts_iff_anyFail_zero
    {n k : Nat}
    (vs : Fin n → LeafVertex I J h)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel (vs i) (ws i))
    (Cvs : ∀ i, CenterSubspace (vs i) k)
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, (Cvs i).K = (Cws i).K)
    (φvs : ∀ i, LeafLabel (vs i))
    (φws : ∀ i, LeafLabel (ws i)) :
    starAccepts vs ws hrel Cvs Cws hK φvs φws ↔
      anyFailIndicator vs ws hrel Cvs Cws hK φvs φws = 0 := by
  unfold starAccepts anyFailIndicator
  split
  · rename_i hex
    constructor
    · intro hagrees
      obtain ⟨i, hi⟩ := hex
      exact (hi (hagrees i)).elim
    · intro hzero
      exact (one_ne_zero hzero).elim
  · rename_i hnex
    constructor
    · intro _
      rfl
    · intro _ i
      by_contra hnot
      exact hnex ⟨i, hnot⟩

theorem starAccepts_of_source_agrees
    {n k : Nat}
    (vs : Fin n → LeafVertex I J h)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel (vs i) (ws i))
    (Cvs : ∀ i, CenterSubspace (vs i) k)
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, (Cvs i).K = (Cws i).K)
    (φvs : ∀ i, LeafLabel (vs i))
    (φws : ∀ i, LeafLabel (ws i))
    (h : ∀ i,
      LinearMap.comp (restrictToCenter (Cvs i) (φvs i))
          (Submodule.inclusion (le_of_eq (hK i).symm)) =
        restrictToCenter (Cws i) (φws i)) :
    starAccepts vs ws hrel Cvs Cws hK φvs φws := by
  intro i
  exact (restrictionAgreesOnCenter_iff_source (hrel i) (Cvs i) (Cws i) (hK i)
    (φvs i) (φws i)).mpr (h i)

/-- Constant-source form of `starAccepts`: one center vertex compared to every queried leaf. -/
def starAcceptsCenter
    {n k : Nat}
    (c : LeafVertex I J h) (Cc : CenterSubspace c k) (ψ : LeafLabel c)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel c (ws i))
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, Cc.K = (Cws i).K)
    (φws : ∀ i, LeafLabel (ws i)) : Prop :=
  ∀ i, restrictionAgreesOnCenter (hrel i) Cc (Cws i) (hK i) ψ (φws i)

theorem starAcceptsCenter_iff_starAccepts
    {n k : Nat}
    (c : LeafVertex I J h) (Cc : CenterSubspace c k) (ψ : LeafLabel c)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel c (ws i))
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, Cc.K = (Cws i).K)
    (φws : ∀ i, LeafLabel (ws i)) :
    starAcceptsCenter c Cc ψ ws hrel Cws hK φws ↔
      starAccepts (fun _ => c) ws hrel (fun _ => Cc) Cws hK (fun _ => ψ) φws :=
  Iff.rfl

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
