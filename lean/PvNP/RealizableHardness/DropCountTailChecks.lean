/- UNCOMPILED intended checks. No axiom output or example success is claimed. -/
import PvNP.RealizableHardness.DropCountTail

namespace PvNP.RealizableHardness.DropCountTailChecks
open scoped BigOperators
open DropCountTail TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence

#print axioms DropCountTail.dropCount_eq_sum
#print axioms DropCountTail.dropCount_cast
#print axioms DropCountTail.tail_sum
#print axioms DropCountTail.tail_nonneg
#print axioms DropCountTail.tail_le_one
#print axioms DropCountTail.block_moment
#print axioms DropCountTail.moment_identity
#print axioms DropCountTail.moment_bound
#print axioms DropCountTail.exponential_tail
#print axioms DropCountTail.optimized_tail
#print axioms DropCountTail.chernoff_tail
#print axioms DropCountTail.tail_zero_of_le
#print axioms DropCountTail.tail_empty
#print axioms DropCountTail.prior_zero_of_drop
#print axioms DropCountTail.tail_beta_zero
#print axioms DropCountTail.tail_mean_zero
#print axioms DropCountTail.chernoff_tail_allow_zero

example : dropped (none : BlockChoice) = 0 := by simp [dropped]
example (k : Fin 3) : dropped (some k) = 1 := by simp [dropped]
example (β : ℚ) : tail β 0 0 = 0 := tail_empty β 0
example (J T : ℕ) : tail 0 J T = 0 := tail_beta_zero J T
example : tail 1 7 7 = 0 := tail_zero_of_le 1 7 7 le_rfl
example : tail (1 / 2) 7 9 = 0 := tail_zero_of_le (1 / 2) 7 9 (by omega)

example (β : ℚ) (J : ℕ) :
    (∑ d : Draw J, (prior β d : ℝ) * Real.exp (0 * dropCount d)) = 1 := by
  simpa using moment_identity β J 0

example : tail (1 / 2) 4 3 ≤ (Real.exp 1 * 2 / 3) ^ 3 := by
  convert chernoff_tail (1 / 2) (by norm_num) (by norm_num) 4 3
    (by norm_num) (by norm_num)
    using 1 <;> norm_num

example : tail (1 / 2) 4 2 ≤ (Real.exp 1 * 2 / 2) ^ 2 := by
  convert chernoff_tail (1 / 2) (by norm_num) (by norm_num) 4 2
    (by norm_num) (by norm_num)
    using 1 <;> norm_num

example : tail 0 4 2 ≤ (Real.exp 1 * (4 * (0 : ℝ)) / 2) ^ 2 := by
  simpa using chernoff_tail_allow_zero 0 (by norm_num) (by norm_num) 4 2
    (by norm_num)

end PvNP.RealizableHardness.DropCountTailChecks
