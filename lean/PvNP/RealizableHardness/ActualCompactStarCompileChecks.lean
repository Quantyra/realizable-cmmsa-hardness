import PvNP.RealizableHardness.ActualCompactStarCompile

/-!
Checks for constructive HN identity-projection stars and manuscript
leaf/alphabet fit.  This file does not inhabit `hSrcCmmsa` and does not
assert unconditional Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualCompactStarCompileChecks

open PvNP.RealizableHardness.ActualCompactStarCompile
open PvNP.RealizableHardness.ActualHeadlineParameters

#check coord_lt
#check compileId
#check compileId_leaves
#check eval_compileId
#check compactData_valid
#check compactData_yes
#check ROf_pos
#check rofSigma_lt_ROf
#check compactLeaves_le
#check paramData_valid
#check paramData_yes

#print axioms compileId_leaves
#print axioms eval_compileId
#print axioms compactData_valid
#print axioms compactData_yes
#print axioms rofSigma_lt_ROf
#print axioms compactLeaves_le
#print axioms paramData_valid
#print axioms paramData_yes

example (L : Nat) : rofSigma L < ROf L :=
  rofSigma_lt_ROf L

example : Formula.leaves (compileId (by decide : 0 < 2) (0 : Fin 2)
    (fun _ : Fin 1 => (1 : Fin 2))) = 4 :=
  compileId_leaves (by decide : 0 < 2) (0 : Fin 2) (fun _ : Fin 1 => (1 : Fin 2))

end PvNP.RealizableHardness.ActualCompactStarCompileChecks
