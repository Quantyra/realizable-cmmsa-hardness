import PvNP.RealizableHardness.FiniteSampling

namespace PvNP.RealizableHardness.FiniteSampling

def thirds (i : ℕ) : ℚ := if i = 0 then 1 / 3 else if i = 1 then 2 / 3 else 0

theorem thirds_nonneg : ∀ i, 0 ≤ thirds i := by
  intro i
  unfold thirds
  split_ifs <;> norm_num

theorem thirds_normalized : cumulative thirds 2 = 1 := by
  norm_num [cumulative, thirds, Finset.sum_range_succ]

theorem fractional_cut_example : cut thirds 8 1 = 2 := by
  have hf : ⌊(8 / 3 : ℚ)⌋₊ = 2 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num [cut, cumulative, thirds, hf]

theorem fractional_mass_example : mass thirds 8 0 = 1 / 4 := by
  rw [mass, roundedCumulative, roundedCumulative, fractional_cut_example]
  norm_num [cut]

theorem rounded_distribution_example :
    (∀ i, 0 ≤ mass thirds 8 i) ∧ (∑ i ∈ Finset.range 2, mass thirds 8 i) = 1 := by
  exact ⟨mass_nonneg thirds 8 thirds_nonneg, mass_sum thirds 8 2 (by omega) thirds_normalized⟩

theorem uniform_event_example (event : ℕ → Bool) :
    |eventMass (mass thirds (2 ^ 8)) 2 event - eventMass thirds 2 event| ≤ (1 / 8 : ℚ) / 8 := by
  apply event_error_of_precision thirds 2 8 (1 / 8) thirds_nonneg (by norm_num)
  norm_num

theorem independent_two_trial_example :
    (∑ draw : Fin 2 → Bool, if (∀ i, draw i = true) then
      trialMass (fun b => if b then (1 / 3 : ℚ) else 2 / 3) 2 draw else 0) = 1 / 9 := by
  rw [trial_event_factorization (fun b => if b then (1 / 3 : ℚ) else 2 / 3) 2 (fun _ b => b)]
  norm_num [Fintype.sum_bool, Fin.prod_univ_two]

theorem one_bit_sampler_example :
    average (fun bits : Fin 1 → Fin 2 => decide (listSampler 1 (fun i => i) bits = 0)) = 1 / 2 := by
  rw [listSampler_exact 1 (fun i => i) (fun i => decide (i = 0))]
  norm_num [average, Fin.sum_univ_two]

#print axioms cumulative_error
#print axioms mass_nonneg
#print axioms mass_error
#print axioms mass_sum
#print axioms event_error
#print axioms event_error_of_precision
#print axioms trialMass_nonneg
#print axioms trialMass_sum
#print axioms trial_event_factorization
#print axioms assignment_count
#print axioms listSampler_exact
#print axioms thirds_nonneg
#print axioms thirds_normalized
#print axioms fractional_cut_example
#print axioms fractional_mass_example
#print axioms rounded_distribution_example
#print axioms uniform_event_example
#print axioms independent_two_trial_example
#print axioms one_bit_sampler_example

end PvNP.RealizableHardness.FiniteSampling