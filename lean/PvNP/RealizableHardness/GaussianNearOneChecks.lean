/- UNCOMPILED checks; no executed axiom reports or examples claimed. -/
import PvNP.RealizableHardness.GaussianNearOne

namespace PvNP.RealizableHardness.GaussianNearOne
open GrassmannCounting GaussianRatio

#print axioms normalizedFrame_nonneg
#print axioms normalizedFrame_mono
#print axioms normalizedFrame_ge_one_sub_error
#print axioms ratio_eq_normalized
#print axioms ratio_eq_product
#print axioms normalized_relative_bounds
#print axioms gaussian_near_one
#print axioms error_le_inverse_pow
#print axioms gaussian_near_one_pow
#print axioms gaussian_probability_ge_half
#print axioms gaussian_near_one_half_J

example (n c : ℕ) : (gaussian (n-c) 0 : ℚ) / gaussian n 0 = 1 := by
  simp [gaussian_zero]

example : (gaussian 0 0 : ℚ) / gaussian 0 0 = 1 := by simp [gaussian_zero]

example (n b : ℕ) (hb : b ≤ n) :
    (gaussian (n-0) b : ℚ) / gaussian n b = 1 := by
  have hg : (gaussian n b : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussian_pos hb)
  simp [hg]

example (n : ℕ) : error n 0 = 0 := by simp [error]

example (c : ℕ) : leading 0 c = 1 := by simp [leading]

example : leading 1 1 / 2 ≤ (gaussian (4-1) 1 : ℚ) / gaussian 4 1 :=
  gaussian_probability_ge_half (by decide) (by decide)

example : leading 2 1 * (1-1/(2:ℚ)^3) ≤
    (gaussian (6-1) 2 : ℚ) / gaussian 6 2 :=
  (gaussian_near_one_pow (by decide) (by decide) (by decide)).1

example (n b c J : ℕ) (hc : c ≤ n) (hb : b+1 ≤ n-c)
    (hJ : b+c+J/2 ≤ n) :
    (gaussian (n-c) b : ℚ) / gaussian n b ≤ leading b c :=
  (gaussian_near_one_half_J hc hb hJ).2

end PvNP.RealizableHardness.GaussianNearOne
