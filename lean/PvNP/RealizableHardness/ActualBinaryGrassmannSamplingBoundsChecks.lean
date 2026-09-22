import PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds

/-!
  D3c2d bounded checks.  The arithmetic fixtures are deliberately concrete
  Gaussian evaluations only; no concrete incidence family is constructed here.
  The checks include b=0, the 7/3/1 tuple, ratio/pair-product endpoints,
  bottom and pointed wrapper signatures, and the explicit exclusion boundary.
-/

namespace PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling

set_option autoImplicit false

#check normalizedFrame
#check normalizedFrame_mono
#check gaussian_ratio_eq
#check gaussian_inverse_ratio_eq
#check gaussian_ratio_lower
#check gaussian_ratio_upper
#check gaussian_probability_ge_half
#check gaussian_probability_ge_inv_nine
#check gaussian_probability_bounds
#check gaussian_pair_product_le
#check bottom_incidenceProbability
#check bottom_incidenceProbability_ge_inv_nine
#check bottom_incidenceMean
#check bottom_pairSubindependent
#check bottom_incidenceSecondMoment_le
#check bottom_incidenceVariance_le_mean
#check bottom_mean_mul_tv_sq_le_one
#check bottom_tv_sq_le_inv_mean
#check bottom_tv_sq_le_nine_dyadic
#check bottom_division_free_chebyshev
#check bottom_rational_chebyshev
#check bottom_dyadic_mean_bounds
#check bottom_badWindow_subset
#check bottom_badWindow_concentration
#check pointed_incidenceProbability
#check pointed_incidenceProbability_ge_inv_nine
#check pointed_incidenceMean
#check pointed_dyadic_mean_bounds
#check pointed_pairSubindependent
#check pointed_incidenceSecondMoment_le
#check pointed_incidenceVariance_le_mean
#check pointed_mean_mul_tv_sq_le_one
#check pointed_tv_sq_le_inv_mean
#check pointed_tv_sq_le_nine_dyadic
#check pointed_division_free_chebyshev
#check pointed_rational_chebyshev
#check pointed_badWindow_subset
#check pointed_badWindow_concentration
#check @bottom_incidenceProbability
#check @bottom_pairSubindependent
#check @pointed_incidenceProbability
#check @pointed_pairSubindependent

example : gaussian 3 0 = 1 := by simp [gaussian_zero]
example : gaussian 3 1 = 7 := by norm_num [gaussian, frameProduct]
example : gaussian 3 2 = 7 := by norm_num [gaussian, frameProduct]
example : gaussian 3 3 = 1 := by simp [gaussian_self]
example : gaussian 2 1 = 3 := by norm_num [gaussian, frameProduct]
example : gaussian 1 0 = 1 := by simp [gaussian_zero]
example : gaussian 1 1 = 1 := by simp [gaussian_self]
example : gaussian (4-2*2) 0 * gaussian 4 0 ≤ gaussian (4-2) 0 ^ 2 := by
  exact gaussian_pair_product_le (b := 0) (n := 4) (r := 2) (by omega)
example : gaussian (4-2*1) 1 * gaussian 4 1 ≤ gaussian (4-1) 1 ^ 2 := by
  exact gaussian_pair_product_le (b := 1) (n := 4) (r := 1) (by omega)
example : gaussian (1-2*1) 0 * gaussian 1 0 ≤ gaussian (1-1) 0 ^ 2 := by
  exact gaussian_pair_product_le (b := 0) (n := 1) (r := 1) (by omega)
example : (gaussian 1 0 : ℚ) / gaussian 1 0 = 1 := by norm_num [gaussian_zero]
example : (gaussian 1 1 : ℚ) ≠ 0 := by norm_num [gaussian_self]
example : (gaussian 2 1 : ℚ) / gaussian 3 1 = 3/7 := by
  norm_num [gaussian, frameProduct]
example : ¬ (1 ≤ 1 - 2*1) := by omega
example : (1 - 2*1 : Nat) = 0 := by norm_num
example : gaussian 0 0 = gaussian (1 - 2*1) 0 := by norm_num [gaussian_zero]

-- Kill-test boundary: the ratio bounds retain their spare-dimension hypotheses.
#check @gaussian_probability_bounds
#check @bottom_badWindow_concentration
#check @pointed_rational_chebyshev

#print axioms gaussian_pair_product_le
#print axioms bottom_pairSubindependent
#print axioms pointed_pairSubindependent
#print axioms bottom_badWindow_concentration
#print axioms pointed_rational_chebyshev
#print axioms bottom_incidenceProbability_ge_inv_nine
#print axioms pointed_incidenceProbability_ge_inv_nine

end PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
