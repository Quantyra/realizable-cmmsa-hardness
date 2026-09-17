import PvNP.RealizableHardness.MatrixGrassmannSpecialization
/-! SOURCE ONLY: no query or example has been executed. -/
open PvNP.RealizableHardness MatrixGrassmannSpecialization

#print axioms slack_range
#print axioms dimensions_add
#print axioms baseDimension_exact
#print axioms extensionWidth_exact
#print axioms half_error_of_growth
#print axioms eventual_actual_half_error
#print axioms eventual_integral_parameters
#print axioms eventual_matrix_grassmann_specialization

set_option pp.fullNames true in
#check eventual_matrix_grassmann_specialization

example : slack 1 4 = (1:ℚ)/4 := rfl
example : scale 4 3 = 12 := rfl
example : baseDimension 1 4 3 = 18 := rfl
example : extensionWidth 1 3 = 6 := rfl
example : baseDimension 1 4 3 + extensionWidth 1 3 = 2*scale 4 3 :=
  dimensions_add (by decide) 3
example : (baseDimension 1 4 3 : ℚ) = 2*(1-slack 1 4)*(scale 4 3 : ℚ) :=
  baseDimension_exact (by decide) (by decide) 3
example : (extensionWidth 1 3 : ℚ) = 2*slack 1 4*(scale 4 3 : ℚ) :=
  extensionWidth_exact (by decide) 3

example (A : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → 0 < h ∧ 2*h ≤ 3*SamplerParameters.blocks A h ∧
      ∀ d w : ℕ, d+w = 2*h →
        ((d+0*w : ℕ):ℝ)*(2:ℝ)^(d+w-1)/(2:ℝ)^(3*SamplerParameters.blocks A h) ≤ 1/2 :=
  eventual_actual_half_error A 0 hA
