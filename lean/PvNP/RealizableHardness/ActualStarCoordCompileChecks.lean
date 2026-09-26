import PvNP.RealizableHardness.ActualStarCoordCompile

/-!
Checks for the star-to-`Fin (n*A)` coordinate adapter.
Does not inhabit `hSrcCmmsa` and does not assert `No σ_L γ_L`.
-/
namespace PvNP.RealizableHardness.ActualStarCoordCompileChecks

open PvNP.RealizableHardness.ActualStarCoordCompile
open PvNP.RealizableHardness.StarListDecoding

#check coord
#check compileStar
#check eval_compileStar
#check idStar
#check idStar_accepts_const
#check idStar_compile_isSome
#check idStar_listWitness_zero

#print axioms eval_compileStar
#print axioms idStar_compile_isSome
#print axioms idStar_listWitness_zero

example : (coord (by decide : 0 < 2) ⟨(0 : Fin 2), (1 : Fin 2)⟩).val = 1 :=
  rfl

end PvNP.RealizableHardness.ActualStarCoordCompileChecks
