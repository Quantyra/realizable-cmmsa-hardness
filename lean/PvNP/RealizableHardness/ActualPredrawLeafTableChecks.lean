import PvNP.RealizableHardness.ActualPredrawLeafTable

namespace PvNP.RealizableHardness.ActualPredrawLeafTableChecks

open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPredrawLeafTable
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualStarAcceptedRankGoodFiber

example {N nRows J h : Nat} {I : Instance N nRows}
    (v : LeafVertex I J h) : Nonempty (LeafLabel v) :=
  leafLabel_nonempty v

example {N nRows J h t : Nat} (I : Instance N nRows)
    (center : QuestionCenter I J t) (D : DomainDraw center h) :
    ∃ T : LeafTable I J h,
      (T (drawVertex center h D)).1.comp (drawEquationInclusion center D) =
        Classical.choose
          (actual_existsUnique_rhsFunctional I center.U center.goodU) := by
  obtain ⟨T, hT⟩ := exists_predraw_leaf_table (J := J) (h := h) I
  exact ⟨T, hT center D⟩

end PvNP.RealizableHardness.ActualPredrawLeafTableChecks
