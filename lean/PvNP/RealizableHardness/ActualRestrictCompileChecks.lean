import PvNP.RealizableHardness.ActualRestrictCompile

/-!
Checks for the restriction-star compiler. Tiny examples first; axiom prints
after those succeed. Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualRestrictCompileChecks

open PvNP.RealizableHardness.ActualRestrictCompile
open PvNP.RealizableHardness.ActualBitRestriction

#check slotVarRes
#check compileRes
#check compileRes_leaves
#check eval_compileRes

example : alph 2 = 16 := rfl

example : Formula.leaves
    (compileRes (by decide : 2 ≤ 2 * 2) (0 : Fin 2) (fun _ : Fin 1 => 1)) =
      32 :=
  compileRes_leaves (by decide : 2 ≤ 2 * 2) (0 : Fin 2) (fun _ : Fin 1 => 1)

#print axioms compileRes_leaves
#print axioms eval_compileRes

end PvNP.RealizableHardness.ActualRestrictCompileChecks
