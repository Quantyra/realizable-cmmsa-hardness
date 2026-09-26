import PvNP.RealizableHardness.ActualBitRestriction

/-!
Checks for large-alphabet bit restriction.  Tiny examples first; axiom
prints only after those succeed.  Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualBitRestrictionChecks

open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.ActualHeadlineParameters

#check alph
#check alph_eq_ROf
#check bit
#check restrictLow
#check restrictLow_ne_id

example : alph 2 = 16 := rfl

example : restrictLow (by decide : 2 ≤ 2 * 2) (⟨5, by decide⟩ : Fin (alph 2)) =
    ⟨1, by decide⟩ :=
  rfl

example : restrictLow (le_of_lt (by decide : 2 < 2 * 2))
    ⟨4, by decide⟩ ≠ (⟨4, by decide⟩ : Fin (alph 2)) :=
  restrictLow_ne_id (by decide : 2 < 2 * 2)

#print axioms alph_eq_ROf
#print axioms restrictLow_ne_id

end PvNP.RealizableHardness.ActualBitRestrictionChecks
