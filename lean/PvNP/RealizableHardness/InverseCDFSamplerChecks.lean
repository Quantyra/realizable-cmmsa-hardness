import PvNP.RealizableHardness.InverseCDFSampler

namespace PvNP.RealizableHardness.InverseCDFSampler
open FiniteSampling

def gapThirds (i : ℕ) : ℚ := if i = 0 then 1 / 3 else if i = 2 then 2 / 3 else 0
lemma gapThirds_nonneg : ∀ i, 0 ≤ gapThirds i := by
  intro i
  unfold gapThirds
  split_ifs <;> norm_num
lemma gapThirds_normalized : cumulative gapThirds 3 = 1 := by
  norm_num [cumulative, gapThirds, Finset.sum_range_succ]
lemma gapThirds_cuts : cut gapThirds 8 1 = 2 ∧ cut gapThirds 8 2 = 2 := by
  have hf : ⌊(8 / 3 : ℚ)⌋₊ = 2 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num [cut, cumulative, gapThirds, Finset.sum_range_succ, hf]

theorem first_seed_example : sampler gapThirds 8 3 gapThirds_normalized ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  apply (sampler_eq_iff _ _ _ _ gapThirds_nonneg _ _).mpr
  constructor
  · simp [cut_zero]
  · change 0 < cut gapThirds 8 1
    rw [gapThirds_cuts.1]
    omega

theorem boundary_seed_example : sampler gapThirds 8 3 gapThirds_normalized ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  apply (sampler_eq_iff _ _ _ _ gapThirds_nonneg _ _).mpr
  constructor
  · simpa using gapThirds_cuts.2.le
  · change 2 < cut gapThirds 8 3
    rw [cut_endpoint _ _ _ gapThirds_normalized]
    omega

theorem final_seed_example : sampler gapThirds 8 3 gapThirds_normalized ⟨7, by omega⟩ = ⟨2, by omega⟩ := by
  apply (sampler_eq_iff _ _ _ _ gapThirds_nonneg _ _).mpr
  constructor
  · change cut gapThirds 8 2 ≤ 7
    rw [gapThirds_cuts.2]
    omega
  · change 7 < cut gapThirds 8 3
    rw [cut_endpoint _ _ _ gapThirds_normalized]
    omega

theorem zero_atom_example :
    Fintype.card {r : Fin 8 // sampler gapThirds 8 3 gapThirds_normalized r = ⟨1, by omega⟩} = 0 := by
  rw [fibre_card _ _ _ _ gapThirds_nonneg]
  change cut gapThirds 8 2 - cut gapThirds 8 1 = 0
  rw [gapThirds_cuts.1, gapThirds_cuts.2]

theorem fractional_fibre_example :
    Fintype.card {r : Fin 8 // sampler gapThirds 8 3 gapThirds_normalized r = ⟨0, by omega⟩} = 2 := by
  rw [fibre_card _ _ _ _ gapThirds_nonneg]
  change cut gapThirds 8 1 - cut gapThirds 8 0 = 2
  rw [gapThirds_cuts.1, cut_zero]

theorem binary_precision_example (event : ℕ → Bool) :
    |average (fun bits : Fin 8 → Fin 2 => event (bitSampler gapThirds 3 8 gapThirds_normalized bits).val) -
      eventMass gapThirds 3 event| ≤ (1 / 8 : ℚ) / 8 := by
  apply bitSampler_event_error _ _ _ _ gapThirds_normalized gapThirds_nonneg (by norm_num)
  norm_num

#print axioms support_pos
#print axioms cut_endpoint
#print axioms sampler_interval
#print axioms sampler_eq_iff
#print axioms fibre_card
#print axioms fibre_probability
#print axioms sampler_event_law
#print axioms bitSampler_event_law
#print axioms bitSampler_event_error
#print axioms gapThirds_nonneg
#print axioms gapThirds_normalized
#print axioms gapThirds_cuts
#print axioms first_seed_example
#print axioms boundary_seed_example
#print axioms final_seed_example
#print axioms zero_atom_example
#print axioms fractional_fibre_example
#print axioms binary_precision_example

end PvNP.RealizableHardness.InverseCDFSampler