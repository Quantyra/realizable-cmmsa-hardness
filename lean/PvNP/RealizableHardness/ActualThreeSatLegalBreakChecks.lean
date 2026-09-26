import PvNP.RealizableHardness.ActualThreeSatLegalBreak

/-!
Checks for low-bit legal3Lin packing that breaks the LegalRes `{0, 2^h}`
two-cover on RHS-1.  Does not inhabit `hSrcCmmsa`.  `{0,1}` still covers
mixed RHS, so this is not a `No σ_L γ_L` map.
-/
namespace PvNP.RealizableHardness.ActualThreeSatLegalBreakChecks

open PvNP.RealizableHardness.ActualThreeSatLegalBreak
open PvNP.RealizableHardness.ActualThreeSatLegalRes
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.CMMSACodec

#check compileLow
#check eval_compileLow
#check legal3Lin_zero
#check legal3Lin_one
#check legal3Lin_highBit_not_one
#check lowResData
#check lowResData_valid
#check lowResData_yes_unit3
#check twoCover_not_eval_rhs1
#check twoCover_not_eval_unsatCnf
#check lowEncFn
#check lowEncFn_mem_FP
#check lowEncFn_ne_id

example : alph 3 = 64 := rfl

#print axioms lowResData_valid
#print axioms lowResData_yes_unit3
#print axioms twoCover_not_eval_rhs1
#print axioms twoCover_not_eval_unsatCnf
#print axioms lowEncFn_mem_FP
#print axioms eval_compileLow

end PvNP.RealizableHardness.ActualThreeSatLegalBreakChecks
