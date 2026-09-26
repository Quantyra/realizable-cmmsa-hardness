import PvNP.RealizableHardness.ActualThreeSatGraphYes

/-!
Checks for packed `Yes 0` of `graphData` and the FP graph encoder.
Tiny examples first; axiom prints after.

Does not inhabit `hSrcCmmsa`.  The FP map is sat-unit `graphData` plus a
tape suffix, so it is not a No-map.  LeafFold/`unsatCnf` is not used.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGraphYesChecks

open PvNP.RealizableHardness.ActualThreeSatGraphYes
open PvNP.RealizableHardness.ActualThreeSatGraphData
open PvNP.RealizableHardness.ActualHeadlineParameters
open Complexity.SAT

#check honestBits_eval_varAt
#check relBits_honest
#check eval_edgeFormula_honest
#check graphData_cost_honest
#check graphData_yes_of_sat
#check paramGraphData_yes_of_sat
#check threeSatToGraphBits_yes_of_sat
#check satUnit
#check satUnitBits_yes
#check threeSatGraphEncFn
#check threeSatGraphEncFn_mem_FP
#check threeSatGraphEncFn_ne_id

example : satUnit.Is3CNF := satUnit_is3

example : CNF.eval [true] satUnit = true := satUnit_sat

example : threeSatGraphEncFn [] ≠ [] := threeSatGraphEncFn_ne_id

#print axioms graphData_yes_of_sat
#print axioms paramGraphData_yes_of_sat
#print axioms threeSatToGraphBits_yes_of_sat
#print axioms satUnitBits_yes
#print axioms threeSatGraphEncFn_mem_FP
#print axioms threeSatGraphEncFn_ne_id
#print axioms eval_edgeFormula_honest
#print axioms graphData_cost_honest

end PvNP.RealizableHardness.ActualThreeSatGraphYesChecks
