import PvNP.RealizableHardness.ActualThreeSatAndAllNo

/-!
Checks for the Grassmann-alphabet AND-all `No` instance.
Tiny examples first; axiom prints after.

Does not inhabit `hSrcCmmsa`.  The FP map is a constant No gadget plus a
tape suffix, so it is not a Yes-map for sat 3SAT.  LeafFold/`unsatCnf`
is not used as a general 3SAT reduction.
-/
namespace PvNP.RealizableHardness.ActualThreeSatAndAllNoChecks

open PvNP.RealizableHardness.ActualThreeSatAndAllNo
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualCompactStarCompile

#check andAllFormula
#check andAllFormula_leaves
#check eval_andAllFormula
#check andAllData
#check andAllData_valid
#check ROf_le_L
#check andAllInstance_no
#check andAllBits_mem_no
#check threeSatNoEncFn
#check threeSatNoEncFn_mem_FP
#check threeSatNoEncFn_ne_id

example (L : Nat) : 0 < ROf L := ROf_pos L

example (L : Nat) : rofSigma L < ROf L := rofSigma_lt_ROf L

#print axioms andAllFormula_leaves
#print axioms eval_andAllFormula
#print axioms andAllData_valid
#print axioms andAllInstance_no
#print axioms andAllBits_mem_no
#print axioms threeSatNoEncFn_mem_FP
#print axioms threeSatNoEncFn_ne_id

end PvNP.RealizableHardness.ActualThreeSatAndAllNoChecks
