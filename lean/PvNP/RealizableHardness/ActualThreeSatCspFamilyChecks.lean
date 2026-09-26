import PvNP.RealizableHardness.ActualThreeSatCspFamily

/-!
Checks for 3SAT-dependent offset-projection stars.
Does not inhabit `hSrcCmmsa` and does not assert `No σ_L γ_L`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCspFamilyChecks

open PvNP.RealizableHardness.ActualThreeSatCspFamily
open PvNP.RealizableHardness.ActualHeadlineParameters

#check addFin
#check compileOff
#check compileOff_leaves
#check clauseStarFormula
#check clauseOff_pos
#check offData_valid
#check paramOffData_valid
#check four_mul_ROf_le

#print axioms compileOff_leaves
#print axioms paramOffData_valid
#print axioms clauseOff_pos
#print axioms four_mul_ROf_le

end PvNP.RealizableHardness.ActualThreeSatCspFamilyChecks
