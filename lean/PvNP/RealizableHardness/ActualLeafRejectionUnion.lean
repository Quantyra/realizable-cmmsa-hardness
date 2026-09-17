import PvNP.RealizableHardness.ActualLeafRepresentativeSampler
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

/-- Transported source restriction agrees with the queried restriction on the shared center. -/
def restrictionAgreesOnCenter
    {v w : LeafVertex I J h} {k : Nat}
    (hvw : LeafVertex.Rel v w)
    (Cv : CenterSubspace v k) (Cw : CenterSubspace w k)
    (hK : Cv.K = Cw.K)
    (φv : LeafLabel v) (φw : LeafLabel w) : Prop :=
  restrictToCenter Cw (transportedLeafLabel hvw φv) = restrictToCenter Cw φw

theorem restrictionAgreesOnCenter_iff_source
    {v w : LeafVertex I J h} {k : Nat}
    (hvw : LeafVertex.Rel v w)
    (Cv : CenterSubspace v k) (Cw : CenterSubspace w k)
    (hK : Cv.K = Cw.K)
    (φv : LeafLabel v) (φw : LeafLabel w) :
    restrictionAgreesOnCenter hvw Cv Cw hK φv φw ↔
      LinearMap.comp (restrictToCenter Cv φv)
          (Submodule.inclusion (le_of_eq hK.symm)) =
        restrictToCenter Cw φw := by
  unfold restrictionAgreesOnCenter
  rw [restrictToCenter_class_invariant hvw Cv Cw hK φv]

/-- `0` if the transported and queried restrictions agree on the shared center, else `1`. -/
noncomputable def leafFailIndicator
    {v w : LeafVertex I J h} {k : Nat}
    (hvw : LeafVertex.Rel v w)
    (Cv : CenterSubspace v k) (Cw : CenterSubspace w k)
    (hK : Cv.K = Cw.K)
    (φv : LeafLabel v) (φw : LeafLabel w) : ℝ :=
  if restrictionAgreesOnCenter hvw Cv Cw hK φv φw then 0 else 1

theorem leafFailIndicator_nonneg
    {v w : LeafVertex I J h} {k : Nat}
    (hvw : LeafVertex.Rel v w)
    (Cv : CenterSubspace v k) (Cw : CenterSubspace w k)
    (hK : Cv.K = Cw.K)
    (φv : LeafLabel v) (φw : LeafLabel w) :
    0 ≤ leafFailIndicator hvw Cv Cw hK φv φw := by
  unfold leafFailIndicator
  split <;> norm_num

theorem leafFailIndicator_le_one
    {v w : LeafVertex I J h} {k : Nat}
    (hvw : LeafVertex.Rel v w)
    (Cv : CenterSubspace v k) (Cw : CenterSubspace w k)
    (hK : Cv.K = Cw.K)
    (φv : LeafLabel v) (φw : LeafLabel w) :
    leafFailIndicator hvw Cv Cw hK φv φw ≤ 1 := by
  unfold leafFailIndicator
  split <;> norm_num

/-- `1` if some queried leaf disagrees on the shared center, else `0`. -/
noncomputable def anyFailIndicator
    {n k : Nat}
    (vs : Fin n → LeafVertex I J h)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel (vs i) (ws i))
    (Cvs : ∀ i, CenterSubspace (vs i) k)
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, (Cvs i).K = (Cws i).K)
    (φvs : ∀ i, LeafLabel (vs i))
    (φws : ∀ i, LeafLabel (ws i)) : ℝ :=
  if ∃ i, ¬ restrictionAgreesOnCenter (hrel i) (Cvs i) (Cws i) (hK i)
        (φvs i) (φws i) then 1 else 0

theorem anyFailIndicator_le_sum
    {n k : Nat}
    (vs : Fin n → LeafVertex I J h)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel (vs i) (ws i))
    (Cvs : ∀ i, CenterSubspace (vs i) k)
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, (Cvs i).K = (Cws i).K)
    (φvs : ∀ i, LeafLabel (vs i))
    (φws : ∀ i, LeafLabel (ws i)) :
    anyFailIndicator vs ws hrel Cvs Cws hK φvs φws ≤
      ∑ i : Fin n, leafFailIndicator (hrel i) (Cvs i) (Cws i) (hK i)
        (φvs i) (φws i) := by
  unfold anyFailIndicator
  split
  · rename_i hex
    obtain ⟨i, hi⟩ := hex
    have hfail :
        leafFailIndicator (hrel i) (Cvs i) (Cws i) (hK i) (φvs i) (φws i) = 1 := by
      unfold leafFailIndicator
      split
      · rename_i hagrees
        exact (hi hagrees).elim
      · rfl
    calc
      (1 : ℝ) = leafFailIndicator (hrel i) (Cvs i) (Cws i) (hK i) (φvs i) (φws i) :=
        hfail.symm
      _ ≤ ∑ j : Fin n, leafFailIndicator (hrel j) (Cvs j) (Cws j) (hK j)
            (φvs j) (φws j) :=
        Finset.single_le_sum
          (fun j _ =>
            leafFailIndicator_nonneg (hrel j) (Cvs j) (Cws j) (hK j)
              (φvs j) (φws j))
          (Finset.mem_univ i)
  · exact Finset.sum_nonneg fun i _ =>
      leafFailIndicator_nonneg (hrel i) (Cvs i) (Cws i) (hK i) (φvs i) (φws i)

theorem anyFailIndicator_le_card
    {n k : Nat}
    (vs : Fin n → LeafVertex I J h)
    (ws : Fin n → LeafVertex I J h)
    (hrel : ∀ i, LeafVertex.Rel (vs i) (ws i))
    (Cvs : ∀ i, CenterSubspace (vs i) k)
    (Cws : ∀ i, CenterSubspace (ws i) k)
    (hK : ∀ i, (Cvs i).K = (Cws i).K)
    (φvs : ∀ i, LeafLabel (vs i))
    (φws : ∀ i, LeafLabel (ws i)) :
    anyFailIndicator vs ws hrel Cvs Cws hK φvs φws ≤ (n : ℝ) := by
  refine (anyFailIndicator_le_sum vs ws hrel Cvs Cws hK φvs φws).trans ?_
  have hle :
      (∑ i : Fin n, leafFailIndicator (hrel i) (Cvs i) (Cws i) (hK i)
        (φvs i) (φws i)) ≤ ∑ _i : Fin n, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ =>
      leafFailIndicator_le_one (hrel i) (Cvs i) (Cws i) (hK i) (φvs i) (φws i)
  refine hle.trans ?_
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
