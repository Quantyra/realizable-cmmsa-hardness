import PvNP.RealizableHardness.ExecutableSamplingPolicy
/-! Draft checks; no compiler acceptance claimed. -/
open PvNP.RealizableHardness ExecutableSamplingPolicy

#print axioms inverse_le
#print axioms inverse_pos
#print axioms self_le_two_pow
#print axioms precision_upper
#print axioms selected_trials_pos
#print axioms selected_grid
#print axioms selected_threshold
#print axioms list_count_le_encode
#print axioms variables_le_input_length
#print axioms rows_le_input_length
#print axioms coinRuler_quadratic
#print axioms selected_coins_le
#print axioms selected_good_probability
#print axioms selected_run_valid
#print axioms digitBool_eq_finTwoEquiv
#print axioms coinBits_eq_flatten
#print axioms padded_seed_probability
#print axioms paddedRunOption_selected
#print axioms ofFn_prefix_split
#print axioms coinBits_unflatten
#print axioms paddedRun_selected_valid
#print axioms padded_length_eq_ruler
#print axioms padded_executor_good_probability
#check @selected_coins_le
#check @selected_run_valid
#check @paddedRun_selected_valid
#check @padded_executor_good_probability

example : inverseCeil (1/4 : Rat) = 4 := by norm_num [inverseCeil]
example : inverseCeil (2/3 : Rat) = 2 := by
  norm_num [inverseCeil]
  have hu : ⌈(3/2 : Rat)⌉₊ ≤ 2 := Nat.ceil_le.mpr (by norm_num)
  have hl := Nat.le_ceil (3/2 : Rat)
  by_contra h
  have hn : ⌈(3/2 : Rat)⌉₊ ≤ 1 := by omega
  have hq : (⌈(3/2 : Rat)⌉₊ : Rat) ≤ 1 := by exact_mod_cast hn
  linarith
example : coinRuler (1/4 : Rat) 0 = 0 := by simp [coinRuler]
example (eps : Rat) (n : Nat) :
    coinRuler eps n = 512 * inverseCeil eps ^ 3 * (n^2+11*n) := coinRuler_quadratic _ _
example (x : ExecutablePipelineInput.Input) :
    x.source.rows.length ≤ (ExecutablePipelineInput.encodeInput x).length := rows_le_input_length x
example : ExecutablePipelineInput.digitBool (0 : Fin 2) = false := rfl
example : ExecutablePipelineInput.digitBool (1 : Fin 2) = true := rfl
example (event : JointSamplingLaw.SeedArray 0 0 → Prop) :
    SeedEncoding.uniformProbability (fun bits : SeedEncoding.FlatSeed (0*0+3) =>
      event (SeedEncoding.unflatten 0 0 (SeedEncoding.takePrefix (0*0) 3 bits))) =
      JointSamplingLaw.seedProbability 0 0 event := padded_seed_probability 0 0 3 event
