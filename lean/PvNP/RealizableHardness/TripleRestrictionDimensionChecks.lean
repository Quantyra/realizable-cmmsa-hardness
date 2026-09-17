/- UNCOMPILED companion source port. No Lean4.34 verification or acceptance has run for this file. -/
import PvNP.RealizableHardness.TripleRestrictionDimension

/-! UNCOMPILED axiom and boundary checks. -/
namespace PvNP.RealizableHardness.TripleRestrictionDimension
open TripleRestrictionRank

#print axioms retainedEquiv
#print axioms retained_finrank_eq_card
#print axioms keptEquiv
#print axioms keptBlock_card
#print axioms keptCoord_card_sum
#print axioms dropCount_sum
#print axioms retained_finrank_add_twice_dropCount
#print axioms twice_dropCount_le
#print axioms retained_finrank_eq
#print axioms dropCount_le
#print axioms dropCount_none
#print axioms dropCount_some
#print axioms retained_finrank_none
#print axioms retained_finrank_some
#print axioms retained_finrank_empty

example (d : Draw 0) : Module.finrank (ZMod 2) (retained d) = 0 :=
  retained_finrank_empty d
example : Module.finrank (ZMod 2) (retained (fun _ : Fin 2 => none)) = 6 := by
  rw [retained_finrank_none]
example : Module.finrank (ZMod 2) (retained (fun _ : Fin 2 => some 0)) = 2 :=
  retained_finrank_some _

def mixedDraw : Draw 2 := fun j => if j = 0 then none else some 1
example : dropCount mixedDraw = 1 := by
  simp [dropCount_sum, mixedDraw, Fin.sum_univ_succ]
example : Module.finrank (ZMod 2) (retained mixedDraw) = 4 := by
  have hd : dropCount mixedDraw = 1 := by
    simp [dropCount_sum, mixedDraw, Fin.sum_univ_succ]
  rw [retained_finrank_eq, hd]

end PvNP.RealizableHardness.TripleRestrictionDimension
