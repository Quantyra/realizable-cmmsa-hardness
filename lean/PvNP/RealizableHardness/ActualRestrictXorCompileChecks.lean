import PvNP.RealizableHardness.ActualRestrictXorCompile

/-!
Checks for affine restriction-star compiler. Tiny examples first.
Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualRestrictXorCompileChecks

open PvNP.RealizableHardness.ActualRestrictXorCompile
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.ActualXorLabel

#check compileResXor
#check compileResXor_leaves
#check eval_compileResXor

example : alph 2 = 16 := rfl

example : Formula.leaves
    (compileResXor (by decide : 2 ≤ 2 * 2) (0 : Fin 2)
      (fun _ : Fin 1 => 1) (fun _ => ⟨0, by decide⟩)) = 32 :=
  compileResXor_leaves (by decide : 2 ≤ 2 * 2) (0 : Fin 2)
    (fun _ : Fin 1 => 1) (fun _ => ⟨0, by decide⟩)

#print axioms compileResXor_leaves
#print axioms eval_compileResXor

end PvNP.RealizableHardness.ActualRestrictXorCompileChecks
