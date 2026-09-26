import PvNP.RealizableHardness.ActualThreeSatStarFamily

/-!
Checks for the 3SAT-dependent large-alphabet polarity-OR family.
Does not inhabit `hSrcCmmsa` and does not assert `No σ_L γ_L` or
unconditional Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarFamilyChecks

open PvNP.RealizableHardness.ActualThreeSatStarFamily
open PvNP.RealizableHardness.ActualHeadlineParameters

#check three_mul_ROf_le
#check paddedClause_leaves
#check starData_valid
#check paramStarData_valid
#check starData_yes_of_sat
#check paramStarData_yes_of_sat
#check hn_zeta_beats_sigma
#check three_le_L_of_mOf

#print axioms three_mul_ROf_le
#print axioms starData_valid
#print axioms paramStarData_valid
#print axioms starData_yes_of_sat
#print axioms paramStarData_yes_of_sat
#print axioms hn_zeta_beats_sigma

example {L : Nat} (h : 256 ≤ mOf L) : 3 * ROf L ≤ L :=
  three_mul_ROf_le h

end PvNP.RealizableHardness.ActualThreeSatStarFamilyChecks
