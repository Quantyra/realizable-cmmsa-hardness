/- UNCOMPILED source draft. No compiler or independent acceptance yet. -/
import PvNP.RealizableHardness.DropTailParameters

/-! The prescribed double-exponential sampler family, with integer A fixed
before h. This discharges the range and mean premises of the numerical tail
specialization. It does not discharge proximity, zoom, or fixed-L assembly. -/
namespace PvNP.RealizableHardness.SamplerParameters

noncomputable section

/-- The exact manuscript ambient block count; neither exponent is rounded. -/
def blocks (A h : ℕ) : ℕ := 2 ^ (2 ^ (A * h ^ 2))

/-- The actual rational probability of deleting a triple. -/
def beta (A h : ℕ) : ℚ := ((A * h ^ 2 : ℕ) : ℚ) / (blocks A h : ℚ)

lemma blocks_pos (A h : ℕ) : 0 < blocks A h := by
  unfold blocks
  positivity

/-- Symbolic exponential growth, including the zero exponent boundary. -/
lemma numerator_lt_blocks (A h : ℕ) : A * h ^ 2 < blocks A h := by
  have h₁ : A * h ^ 2 < 2 ^ (A * h ^ 2) := Nat.lt_two_pow_self
  have h₂ : 2 ^ (A * h ^ 2) < 2 ^ (2 ^ (A * h ^ 2)) := Nat.lt_two_pow_self
  exact h₁.trans h₂

lemma beta_nonneg (A h : ℕ) : 0 ≤ beta A h := by
  unfold beta
  positivity

lemma beta_lt_one (A h : ℕ) : beta A h < 1 := by
  have hp : (0 : ℚ) < blocks A h := by exact_mod_cast blocks_pos A h
  apply (div_lt_iff₀ hp).mpr
  simpa only [one_mul] using
    (show ((A * h ^ 2 : ℕ) : ℚ) < (blocks A h : ℚ) by
      exact_mod_cast numerator_lt_blocks A h)

lemma beta_le_one (A h : ℕ) : beta A h ≤ 1 := (beta_lt_one A h).le

lemma beta_pos {A h : ℕ} (hA : 0 < A) (hh : 0 < h) : 0 < beta A h := by
  unfold beta
  exact div_pos (by exact_mod_cast Nat.mul_pos hA (pow_pos hh 2))
    (by exact_mod_cast blocks_pos A h)

lemma mean_rat (A h : ℕ) :
    (blocks A h : ℚ) * beta A h = (A : ℚ) * (h : ℚ) ^ 2 := by
  have hz : (blocks A h : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast blocks_pos A h)
  unfold beta
  push_cast
  field_simp [hz]

lemma mean_real (A h : ℕ) :
    (blocks A h : ℝ) * (beta A h : ℝ) = (A : ℝ) * (h : ℝ) ^ 2 := by
  exact_mod_cast mean_rat A h

lemma blocks_zero_A (h : ℕ) : blocks 0 h = 2 := by simp [blocks]

lemma blocks_zero_h (A : ℕ) : blocks A 0 = 2 := by simp [blocks]

lemma beta_zero_A (h : ℕ) : beta 0 h = 0 := by simp [beta]

lemma beta_zero_h (A : ℕ) : beta A 0 = 0 := by simp [beta]

lemma beta_eq_zero_iff (A h : ℕ) : beta A h = 0 ↔ A = 0 ∨ h = 0 := by
  have hz : (blocks A h : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast blocks_pos A h)
  simp [beta, hz]

/-- The existing actual deletion-event tail with every sampler premise proved. -/
theorem actual_tail {A h : ℕ} (hr : DropTailParameters.Ready (A : ℝ) h) :
    DropCountTail.tail (beta A h) (blocks A h) (h ^ 4) ≤
      DropTailParameters.decay 100 h := by
  exact DropTailParameters.actual_tail (by positivity)
    (beta_nonneg A h) (beta_le_one A h) hr (mean_real A h)

theorem actual_tail_over_zeta {A h : ℕ}
    (hr : DropTailParameters.Ready (A : ℝ) h) :
    DropCountTail.tail (beta A h) (blocks A h) (h ^ 4) /
        DropTailParameters.decay 30 h ≤ DropTailParameters.decay 70 h := by
  exact DropTailParameters.actual_tail_over_zeta (by positivity)
    (beta_nonneg A h) (beta_le_one A h) hr (mean_real A h)

/-- For every fixed positive integer A, one threshold works for all later h.
There is no supplied beta-range, mean identity, small-tail, or growth premise. -/
theorem eventual_actual_tail (A : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h →
      DropCountTail.tail (beta A h) (blocks A h) (h ^ 4) ≤
          DropTailParameters.decay 100 h ∧
      DropCountTail.tail (beta A h) (blocks A h) (h ^ 4) /
          DropTailParameters.decay 30 h ≤ DropTailParameters.decay 70 h := by
  obtain ⟨N, hN⟩ := DropTailParameters.eventual_actual_tail
    (A : ℝ) (by exact_mod_cast hA)
  refine ⟨N, ?_⟩
  intro h hh
  exact (hN h hh).2.2 (blocks A h) (beta A h)
    (beta_nonneg A h) (beta_le_one A h) (mean_real A h)

end
end PvNP.RealizableHardness.SamplerParameters
