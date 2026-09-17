/- UNCOMPILED companion source port. No Lean4.34 verification or acceptance has run for this file. -/
import PvNP.RealizableHardness.GrassmannCounting

/-! UNCOMPILED checks for exact finite subspace cardinalities. -/
namespace PvNP.RealizableHardness.GrassmannCounting
open TripleRestrictionRank

#print axioms span_flatten
#print axioms flatten_injective
#print axioms flatten_surjective
#print axioms frameEquiv
#print axioms card_frame
#print axioms card_internal_frame
#print axioms card_grass_mul
#print axioms frameProduct_self_pos
#print axioms card_grass_of_le
#print axioms card_grass_of_lt
#print axioms card_grass
#print axioms gaussian_zero
#print axioms gaussian_of_lt
#print axioms gaussian_self
#print axioms include_injective
#print axioms include_surjective
#print axioms containedEquiv
#print axioms card_contained
#print axioms incidenceCount_eq
#print axioms incidenceCount_zero
#print axioms incidenceCount_of_lt

example (n : ℕ) : gaussian n 0 = 1 := gaussian_zero n
example : gaussian 0 0 = 1 := gaussian_zero 0
example : gaussian 0 1 = 0 := gaussian_of_lt (by decide)
example (n : ℕ) : gaussian n (n + 1) = 0 := gaussian_of_lt (Nat.lt_succ_self n)
example (n : ℕ) : gaussian n n = 1 := gaussian_self n

example : gaussian 3 1 = 7 := by
  norm_num [gaussian, frameProduct, Fin.prod_univ_succ]
example : gaussian 3 2 = 7 := by
  norm_num [gaussian, frameProduct, Fin.prod_univ_succ]

example : Fintype.card (Grass (Fin 3 → ZMod 2) 1) = 7 := by
  rw [card_grass]
  norm_num [Module.finrank_pi, gaussian, frameProduct, Fin.prod_univ_succ]

example : Fintype.card (Grass (Fin 0 → ZMod 2) 0) = 1 := by
  rw [card_grass, gaussian_zero]

example : Fintype.card (Grass (Fin 0 → ZMod 2) 1) = 0 := by
  apply card_grass_of_lt
  simp [Module.finrank_pi]

example (d : Draw 0) : GrassmannIncidence.incidenceCount d 0 = 1 :=
  incidenceCount_zero d

example (d : Draw J) :
    GrassmannIncidence.incidenceCount d (Module.finrank (ZMod 2) (retained d) + 1) = 0 :=
  incidenceCount_of_lt d (Nat.lt_succ_self _)

end PvNP.RealizableHardness.GrassmannCounting
