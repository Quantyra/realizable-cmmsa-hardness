import PvNP.RealizableHardness.ActualXorLabel

/-!
Checks for affine XOR on large-alphabet labels. Tiny examples first.
Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualXorLabelChecks

open PvNP.RealizableHardness.ActualXorLabel
open PvNP.RealizableHardness.ActualBitRestriction

#check xorFin
#check xorFin_comm
#check xorFin_self
#check xorFin_zero

example : alph 2 = 16 := rfl

example : xorFin (⟨5, by decide⟩ : Fin (alph 2)) ⟨3, by decide⟩ =
    ⟨6, by decide⟩ :=
  rfl

example : xorFin (⟨5, by decide⟩ : Fin (alph 2)) ⟨5, by decide⟩ =
    ⟨0, by decide⟩ :=
  xorFin_self _

#print axioms xorFin_self
#print axioms xorFin_zero

end PvNP.RealizableHardness.ActualXorLabelChecks
