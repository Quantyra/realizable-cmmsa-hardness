/- UNCOMPILED checks: all profiles and examples below still require compilation. -/
import PvNP.RealizableHardness.DropTailParameters

open PvNP.RealizableHardness.DropTailParameters

#print axioms decay_eq_reciprocal
#print axioms decay_pos
#print axioms decay_zero
#print axioms decay_add
#print axioms decay_ratio
#print axioms ready_h_pos
#print axioms eventually_ready
#print axioms mean_le_cutoff
#print axioms chernoff_base_le_half
#print axioms cutoff_dominates
#print axioms numerical_chernoff
#print axioms chernoff_base_rewrite
#print axioms actual_tail
#print axioms actual_tail_over_zeta
#print axioms eventual_actual_tail

example : decay 100 0 / decay 30 0 = 1 := by simp [decay]
example : decay 1 1 = (1 / 2 : ℝ) := by norm_num [decay]
example : decay 2 1 = (1 / 4 : ℝ) := by norm_num [decay]
example : Ready 0 10 := by norm_num [Ready]
example (A : ℝ) : ¬ Ready A 0 := by simp [Ready]
example (h : ℕ) : decay 100 h / decay 30 h = decay 70 h := decay_ratio h
example (J : ℕ) : PvNP.RealizableHardness.DropCountTail.tail 0 J (10 ^ 4) ≤
    decay 100 10 := by
  apply actual_tail (A := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Ready])
  simp
