import PvNP.RealizableHardness.ActualVecLabel

/-!
Checks for the F2^{2h} label chart. Tiny examples first; axiom prints after.
Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualVecLabelChecks

open PvNP.RealizableHardness.ActualVecLabel
open PvNP.RealizableHardness.ActualBitRestriction

#check vecOfFin
#check finOfVec
#check finOfBits_lt
#check vecOfFin_zero

example : alph 2 = 16 := rfl

example : vecOfFin (h := 2) ⟨0, by decide⟩ 0 = 0 := by
  simp [vecOfFin_zero]

#print axioms finOfBits_lt
#print axioms vecOfFin_zero

end PvNP.RealizableHardness.ActualVecLabelChecks
