import PvNP.RealizableHardness.ActualThreeSatGrassmannFan

/-!
Checks for overlapping three-leaf shift-fan packing.  `sevenCover` and
`cheapTwo` fail RHS-1.  Remaining vertex-dependent 2-list `vdFan` still
covers: not `No σ_L γ_L`, not `hSrcCmmsa`.  Not `compileRotate` /
`sevenCover` / `compileOverlap` / `fourCover`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGrassmannFanChecks

open PvNP.RealizableHardness.ActualThreeSatGrassmannFan
open PvNP.RealizableHardness.ActualThreeSatRotate
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.CMMSACodec

#check restrictShift
#check restrictShift_ne_id
#check restrictShift_dualBit
#check restrictShift_id
#check compileFan
#check eval_compileFan
#check sevenCover_not_eval_rhs1
#check sevenCover_not_eval_unsatCnf
#check cheapTwo_not_eval_rhs1
#check cheapTwo_not_eval_unsatCnf
#check vdFan_eval_rhs1
#check fanData_valid
#check fanData_yes_unit3
#check fanEncFn
#check fanEncFn_mem_FP
#check fanEncFn_ne_id

example : alph 4 = 256 := rfl

#print axioms eval_compileFan
#print axioms restrictShift_dualBit
#print axioms sevenCover_not_eval_rhs1
#print axioms cheapTwo_not_eval_rhs1
#print axioms vdFan_eval_rhs1
#print axioms fanData_yes_unit3
#print axioms fanEncFn_mem_FP
#print axioms restrictShift_ne_id

end PvNP.RealizableHardness.ActualThreeSatGrassmannFanChecks
