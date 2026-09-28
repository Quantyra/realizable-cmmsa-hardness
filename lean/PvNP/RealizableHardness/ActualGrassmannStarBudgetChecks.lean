import PvNP.RealizableHardness.ActualCompiledProductChecks
import PvNP.RealizableHardness.ActualGrassmannStarBudget

/-!
Checks for the Grassmann star budget. The examples call the shipped
theorems, including `assignmentCost_true` on the existing toy star.
Axioms print after. This file does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannStarBudgetChecks

open ActualGrassmannStarBudget
open ActualCompiledProduct
open ActualCompiledProductChecks
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarCmmsaSemantics

noncomputable section

#check assignmentCost_true
#check uniform_rBlock_starBudget
#check rBlock_starBudget_outside_all_true

example :
    assignmentCost uniformEdge toyEdges (fun _ => true) = 1 :=
  assignmentCost_true uniformEdge uniformEdge_nonneg uniformEdge_sum toyEdges

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
        {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]
        (edges : E → Star V Sigma (certifiedM L))
        (hR : ∀ v, Fintype.card (Sigma v) = RBlock L (certifiedM L)),
        (manuscriptSigma L : ℝ) * starBudget uniformEdge edges <
          assignmentCost uniformEdge edges (fun _ => true) :=
  rBlock_starBudget_outside_all_true

#print axioms assignmentCost_true
#print axioms uniform_rBlock_starBudget
#print axioms rBlock_starBudget_outside_all_true

end

end PvNP.RealizableHardness.ActualGrassmannStarBudgetChecks
