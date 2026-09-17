import PvNP.RealizableHardness.ComputableSampleCount
namespace PvNP.RealizableHardness.ComputableSampleCount

theorem concrete_count_small : count 0 1 = 512 := by
  have hu : Nat.clog 2 352 <= 9 :=
    (Nat.clog_le_iff_le_pow (b := 2) (x := 352) (y := 9) (by decide)).mpr (by decide)
  have hl : 8 < Nat.clog 2 352 :=
    (Nat.lt_clog_iff_pow_lt (b := 2) (x := 352) (y := 8) (by decide)).mpr (by decide)
  have he : Nat.clog 2 352 = 9 := by omega
  change (2 ^ Nat.clog 2 352 : Nat) = 512
  rw [he]
  decide

theorem concrete_count_half : count 3 2 = 2048 := by
  have ht : target 3 2 = 1792 := by norm_num [target]
  have hu : Nat.clog 2 1792 <= 11 :=
    (Nat.clog_le_iff_le_pow (b := 2) (x := 1792) (y := 11) (by norm_num)).mpr (by norm_num)
  have hl : 10 < Nat.clog 2 1792 :=
    (Nat.lt_clog_iff_pow_lt (b := 2) (x := 1792) (y := 10) (by norm_num)).mpr (by norm_num)
  have hc : Nat.clog 2 1792 = 11 := by omega
  have he : exponent 3 2 = 11 := (congrArg (Nat.clog 2) ht).trans hc
  exact (count_power_two 3 2).trans
    ((congrArg (fun k : Nat => 2 ^ k) he).trans (by norm_num))

theorem concrete_count_zero : count 0 0 = 1 := by
  have ht : target 0 0 = 0 := by norm_num [target]
  have he : exponent 0 0 = 0 := (congrArg (Nat.clog 2) ht).trans (Nat.clog_zero_right 2)
  exact (count_power_two 0 0).trans
    ((congrArg (fun k : Nat => 2 ^ k) he).trans (by norm_num))

-- Executed evaluations supplement the proved equalities; no native_decide proof.
#eval count 0 1
#eval count 3 2
#eval count 0 0

theorem concrete_half_error :
    SamplingThreshold.learningThreshold 3 (1 / 2) <= (count 3 2 : Real) := by
  apply learningThreshold_le_count <;> norm_num

theorem concrete_small_error :
    SamplingThreshold.threshold 5 (1 / 100) <= (count 5 100 : Real) := by
  apply threshold_le_count <;> norm_num

#print axioms concrete_count_small
#print axioms concrete_count_half
#print axioms concrete_count_zero
#print axioms count_pos
#print axioms count_power_two
#print axioms target_le_count
#print axioms target_gt_one
#print axioms count_upper
#print axioms learningThreshold_le_target
#print axioms learningThreshold_le_count
#print axioms threshold_le_count
#print axioms inverse_bound_pos
#print axioms count_upper_of_inverse
#print axioms learning_budget
#print axioms base_budget
#print axioms concrete_half_error
#print axioms concrete_small_error
end PvNP.RealizableHardness.ComputableSampleCount
