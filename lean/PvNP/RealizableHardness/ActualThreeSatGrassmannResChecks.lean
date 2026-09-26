import PvNP.RealizableHardness.ActualThreeSatGrassmannRes

/-!
Checks for 3SAT-dependent m-ary Grassmann restriction-star packing.
Does not inhabit `hSrcCmmsa`.  Restriction stars remain Yes on unsat.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGrassmannResChecks

open PvNP.RealizableHardness.ActualThreeSatGrassmannRes
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.CMMSACodec

#check resStarData
#check resStarData_valid
#check resStarData_yes
#check resStarData_not_no
#check resStarData_yes_mem
#check res_proj_ne_id
#check resFormula_leaves

example : alph 2 = 16 := rfl

#print axioms resStarData_valid
#print axioms resStarData_yes
#print axioms resStarData_not_no
#print axioms resStarData_yes_mem
#print axioms res_proj_ne_id

end PvNP.RealizableHardness.ActualThreeSatGrassmannResChecks
