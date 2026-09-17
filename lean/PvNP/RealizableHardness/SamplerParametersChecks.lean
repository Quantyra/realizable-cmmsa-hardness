/- UNCOMPILED checks. No validation is claimed. -/
import PvNP.RealizableHardness.SamplerParameters

open PvNP.RealizableHardness
open PvNP.RealizableHardness.SamplerParameters

#print axioms blocks_pos
#print axioms numerator_lt_blocks
#print axioms beta_nonneg
#print axioms beta_lt_one
#print axioms beta_le_one
#print axioms beta_pos
#print axioms mean_rat
#print axioms mean_real
#print axioms blocks_zero_A
#print axioms blocks_zero_h
#print axioms beta_zero_A
#print axioms beta_zero_h
#print axioms beta_eq_zero_iff
#print axioms actual_tail
#print axioms actual_tail_over_zeta
#print axioms eventual_actual_tail

example : blocks 0 0 = 2 := blocks_zero_A 0
example (A : ℕ) : beta A 0 = 0 := beta_zero_h A
example (h : ℕ) : beta 0 h = 0 := beta_zero_A h
example : blocks 1 1 = 4 := by norm_num [blocks]
example : beta 1 1 = 1 / 4 := by norm_num [beta, blocks]
example : (0 : ℚ) < beta 1 1 := beta_pos (by decide) (by decide)
example (A h : ℕ) : (blocks A h : ℝ) * (beta A h : ℝ) =
    (A : ℝ) * (h : ℝ) ^ 2 := mean_real A h
example : ∃ N : ℕ, ∀ h : ℕ, N ≤ h →
    DropCountTail.tail (beta 1 h) (blocks 1 h) (h ^ 4) ≤
        DropTailParameters.decay 100 h ∧
    DropCountTail.tail (beta 1 h) (blocks 1 h) (h ^ 4) /
        DropTailParameters.decay 30 h ≤ DropTailParameters.decay 70 h :=
  eventual_actual_tail 1 (by decide)
