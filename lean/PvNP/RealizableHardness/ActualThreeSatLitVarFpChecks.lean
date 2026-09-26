import PvNP.RealizableHardness.ActualThreeSatLitVarFp

/-!
Checks for the thin `litVarFn` FP composition.

Does not inhabit `hSrcCmmsa`.  Does not pack a Yes/No CMMSA instance.
-/
namespace PvNP.RealizableHardness.ActualThreeSatLitVarFpChecks

open PvNP.RealizableHardness.ActualThreeSatLitVarFp
open Complexity

#check slotArgFn
#check slotArgFn_mem_FP
#check clauseLitVarFn
#check clauseLitVarFn_mem_FP

example : clauseLitVarFn 0 0 ∈ Complexity.FP := clauseLitVarFn_mem_FP 0 0

example : clauseLitVarFn 1 2 ∈ Complexity.FP := clauseLitVarFn_mem_FP 1 2

#print axioms slotArgFn_mem_FP
#print axioms clauseLitVarFn_mem_FP

end PvNP.RealizableHardness.ActualThreeSatLitVarFpChecks
