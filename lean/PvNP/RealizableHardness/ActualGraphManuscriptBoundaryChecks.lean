import PvNP.RealizableHardness.ActualGraphManuscriptBoundary

/-!
Checks for the constraint-graph encoding at manuscript parameters.
The example calls the shipped yes and not-no theorems on `satUnit` and
`falseFormula`.
-/
namespace PvNP.RealizableHardness.ActualGraphManuscriptBoundaryChecks

open ActualGraphManuscriptBoundary
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualThreeSatGraphData
open ActualThreeSatGraphYes
open CMMSACodec
open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hm : 256 ≤ mOf L) (hσ : 1 ≤ manuscriptSigma L) (_hσ2 : 2 ≤ manuscriptSigma L)
        (hγ0 : 0 < manuscriptGamma L) (hγ1 : manuscriptGamma L < 1),
        threeSatToGraphBits hm satUnit satUnit_is3 satUnit_len ∈
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).yesInstances ∧
          threeSatToGraphBits hm falseFormula falseFormula_is3CNF falseFormula_len ∉
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).noInstances :=
  graph_manuscript_yes_sat_not_no_unsat

#print axioms graph_bits_manuscript_yes_satUnit
#print axioms graph_bits_manuscript_false_not_no
#print axioms graph_manuscript_yes_sat_not_no_unsat

end PvNP.RealizableHardness.ActualGraphManuscriptBoundaryChecks
