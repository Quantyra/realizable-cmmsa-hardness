import PvNP.RealizableHardness.ActualTaggedFixedUDensityForce

/-! The exact numerical comparison between the fixed-table high-density
selection level and the robust MZ local decoder's `8S` input. The physical
score premise `Δ/2` remains separate from this arithmetic. -/

namespace PvNP.RealizableHardness.ActualTaggedMZThresholdArithmetic

set_option autoImplicit false
noncomputable section

/-- `α = Δ/2`, `S = 2⁻ᵖ`, `Δ = 2⁻ᑫ`, and the class collision loss is
`2⁻ᴶ`. The manuscript's large-`h` strict slack is encoded by `q+6 ≤ p`;
the borderline `q+5 ≤ p` alone leaves no room for a positive collision
loss when equality holds. -/
theorem halfValue_collision_beta_ge_eightS {J p q : Nat}
    (hgap : q + 6 ≤ p) (hpJ : p ≤ J) :
    8 * (1 / 2 : ℚ) ^ p ≤
      (((1 / 2 : ℚ) ^ (q + 1) - (1 / 2 : ℚ) ^ J) / 2) := by
  have hJp : (1 / 2 : ℚ) ^ J ≤ (1 / 2 : ℚ) ^ p :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hpJ
  have hpq : (1 / 2 : ℚ) ^ p ≤ (1 / 2 : ℚ) ^ (q + 6) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap
  rw [pow_add] at hpq ⊢
  have hbase : 0 ≤ (1 / 2 : ℚ) ^ q := by positivity
  norm_num at hpq ⊢
  nlinarith

/-- The manuscript exponents imply the required six-bit margin for
`ξ = 4000ρ` once `h` clears the stated fixed-parameter cutoff. -/
theorem realExponent_halfValue_collision_beta_ge_eightS
    {J : Nat} {p q : ℝ}
    (hgap : q + 6 ≤ p) (hpJ : p ≤ J) :
    8 * (1 / 2 : ℝ) ^ p ≤
      (((1 / 2 : ℝ) ^ (q + 1) - (1 / 2 : ℝ) ^ (J : ℝ)) / 2) := by
  have hJp : (1 / 2 : ℝ) ^ (J : ℝ) ≤ (1 / 2 : ℝ) ^ p :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hpJ
  rw [Real.rpow_natCast] at hJp
  have hpq : (1 / 2 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ (q + 6) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hgap
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) q 6] at hpq
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) q 1]
  have hbase : 0 ≤ (1 / 2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  norm_num at hpq ⊢
  nlinarith

/-- The actual manuscript exponent quantifiers are real: `ρ` may be
shrunk after `ξ` is fixed. Its sufficient large-`h` inequality gives a
strict extra bit beyond the displayed `Δ/S ≥ 32` boundary, which pays
for the positive class-collision loss. -/
theorem manuscript_realExponent_halfValue_collision_beta_ge_eightS
    {J h m : Nat} (ξ ρ : ℝ)
    (hξ : 4000 * ρ ≤ ξ)
    (hlarge : (6 : ℝ) ≤ 2 * h * m * (ξ - 1000 * ρ))
    (hpJ : 2 * (1 - 1000 * ρ) * h * m ≤ (J : ℝ)) :
    let S := (1 / 2 : ℝ) ^ (2 * (1 - 1000 * ρ) * h * m)
    let Δ := (1 / 2 : ℝ) ^ (2 * (1 - ξ) * h * m)
    8 * S ≤ ((Δ / 2 - (1 / 2 : ℝ) ^ (J : ℝ)) / 2) := by
  dsimp
  have hgap : 2 * (1 - ξ) * h * m + 6 ≤
      2 * (1 - 1000 * ρ) * h * m := by
    nlinarith [hlarge]
  have hbound := realExponent_halfValue_collision_beta_ge_eightS hgap hpJ
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)
    (2 * (1 - ξ) * h * m) 1] at hbound
  norm_num at hbound
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hbound

end
end PvNP.RealizableHardness.ActualTaggedMZThresholdArithmetic
