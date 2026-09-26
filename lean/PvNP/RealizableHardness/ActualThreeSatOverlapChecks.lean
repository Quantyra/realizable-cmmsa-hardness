import PvNP.RealizableHardness.ActualThreeSatOverlap

/-!
Checks for overlapping high-bit restriction.  Vertex-dependent 2-list
`vdCover` fails RHS-1.  Remaining 4-hot still covers: not `No σ_L γ_L`,
not `hSrcCmmsa`.  Not `compileMid` / `threeCover` / `twoHot`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatOverlapChecks

open PvNP.RealizableHardness.ActualThreeSatOverlap
open PvNP.RealizableHardness.ActualThreeSatHalfWidth
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction

#check restrictHigh
#check restrictHigh_ne_id
#check restrictHigh_dualBit
#check compileOverlap
#check eval_compileOverlap
#check vdCover_not_eval_rhs1
#check vdCover_not_eval_unsatCnf
#check fourCover_eval_rhs1
#check fourCover_eval_unsatCnf_rhs1
#check overlapEncFn
#check overlapEncFn_mem_FP
#check overlapEncFn_ne_id

example : alph 3 = 64 := rfl

#print axioms eval_compileOverlap
#print axioms restrictHigh_dualBit
#print axioms vdCover_not_eval_rhs1
#print axioms fourCover_eval_rhs1
#print axioms overlapEncFn_mem_FP
#print axioms restrictHigh_ne_id

end PvNP.RealizableHardness.ActualThreeSatOverlapChecks
