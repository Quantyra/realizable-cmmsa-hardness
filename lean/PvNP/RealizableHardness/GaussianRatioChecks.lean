/- UNCOMPILED checks: these are intended commands, not axiom or evaluation results. -/
import PvNP.RealizableHardness.GaussianRatio

namespace PvNP.RealizableHardness.GaussianRatio
open GrassmannCounting TripleRestrictionRank TripleRestrictionDimension

#print axioms sum_two_pow
#print axioms one_sub_sum_le_prod
#print axioms normalizedFrame_le_one
#print axioms normalizedFrame_ge_half
#print axioms cast_frameProduct
#print axioms gaussian_mul_frame
#print axioms frameProduct_pos
#print axioms gaussian_pos
#print axioms gaussian_ratio_eq
#print axioms gaussian_ratio_le
#print axioms retained_gaussian_ratio_le
#print axioms retained_gaussian_twice_le_cutoff

example (n m : ℕ) : (gaussian n 0 : ℚ) / gaussian m 0 = 1 := by
  simp [gaussian_zero]

example : normalizedFrame 0 0 = 1 := by simp [normalizedFrame]

example : (1 / 2 : ℚ) ≤ normalizedFrame 2 1 :=
  normalizedFrame_ge_half (by decide)

example : (gaussian 3 1 : ℚ) / gaussian 2 1 ≤ 2 * (2 : ℚ)^(1*(3-2)) :=
  gaussian_ratio_le (by decide) (by decide)

/-- The first bound requires spare dimension; exact counting covers the diagonal. -/
example (a : ℕ) : gaussian a a = 1 := gaussian_self a

example (n a : ℕ) (h : n < a) : gaussian n a = 0 := gaussian_of_lt h

example (draw : Draw J) (hJ : a + 1 ≤ J) (hT : dropCount draw ≤ T) :
    2 * ((gaussian (3*J) a : ℚ) /
      gaussian (Module.finrank (ZMod 2) (retained draw)) a) ≤
        8 * (2 : ℚ)^(2*a*T) := by
  apply retained_gaussian_twice_le_cutoff draw _ hT
  have hd := dropCount_le draw
  omega

end PvNP.RealizableHardness.GaussianRatio
