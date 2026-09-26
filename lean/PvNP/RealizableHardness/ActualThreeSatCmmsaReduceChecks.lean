import PvNP.RealizableHardness.ActualThreeSatCmmsaReduce

/-!
Checks for the semantic 3SAT → CMMSA polarity-OR compiler, including
`Yes 0` completeness and the matching not-No fact.  Does not inhabit
`hSrcCmmsa` and does not assert unconditional Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCmmsaReduceChecks

open PvNP.RealizableHardness.ActualThreeSatCmmsaReduce
open PvNP.RealizableHardness.CMMSACodec
open PvNP.RealizableHardness.CMMSAEncoding
open PvNP.RealizableHardness.ActualHeadlineParameters
open Complexity.SAT

#check nPol_pos
#check litIndex
#check clauseFormula_leaves
#check compileWeights_sum
#check compileData_valid
#check compileData_yes_of_sat
#check compileData_not_no
#check compileDataBudget_not_no_of_half
#check unit3_yes

example (hL : 3 ≤ (128 : Nat)) :
    Yes 0 (ofData (compileData unit3 unit3_is3 unit3_len)
      (compileData_valid unit3 unit3_is3 unit3_len hL)) :=
  unit3_yes hL

example {L : Nat} (hσ : 1 ≤ rofSigma L) (hγ1 : gammaL L < 1) (hL : 3 ≤ L) :
    ¬ No (rofSigma L) (gammaL L)
      (ofData (compileData unit3 unit3_is3 unit3_len)
        (compileData_valid unit3 unit3_is3 unit3_len hL)) :=
  compileData_not_no hσ hγ1 unit3 unit3_is3 unit3_len hL

#print axioms compileData_valid
#print axioms compileData_yes_of_sat
#print axioms compileData_not_no
#print axioms compileDataBudget_not_no_of_half
#print axioms unit3_yes
#print axioms clauseFormula_leaves
#print axioms compileWeights_sum

end PvNP.RealizableHardness.ActualThreeSatCmmsaReduceChecks
