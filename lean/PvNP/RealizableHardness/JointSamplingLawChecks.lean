import PvNP.RealizableHardness.JointSamplingLaw

namespace PvNP.RealizableHardness.JointSamplingLaw
open scoped BigOperators
open FiniteSampling InverseCDFSampler

def halfWithZero (i : Nat) : Rat := if i < 2 then 1 / 2 else 0
lemma half_nonneg : forall i, 0 <= halfWithZero i := by
  intro i
  unfold halfWithZero
  split_ifs <;> norm_num
lemma half_normalized : cumulative halfWithZero 3 = 1 := by
  norm_num [cumulative, halfWithZero, Finset.sum_range_succ]
lemma half_mass (i : Fin 3) : mass halfWithZero 2 i.val = if i.val < 2 then 1 / 2 else 0 := by
  fin_cases i <;> norm_num [mass, roundedCumulative, cut, cumulative, halfWithZero, Finset.sum_range_succ]

/-- Equality of two independent outputs is not a rectangular event. -/
theorem two_trial_diagonal :
    average (fun seeds : SeedArray 2 1 =>
      decide (sampleArray halfWithZero 3 1 2 half_normalized seeds 0 =
        sampleArray halfWithZero 3 1 2 half_normalized seeds 1)) = (1 / 2 : Rat) := by
  rw [sampleArray_event_law halfWithZero 3 1 2 half_normalized half_nonneg (fun x => decide (x 0 = x 1))]
  have he := (finTwoArrowEquiv (Fin 3)).symm.sum_comp
    (fun x : Fin 2 -> Fin 3 => if decide (x 0 = x 1) then
      trialMass (fun i : Fin 3 => mass halfWithZero (2 ^ 1) i.val) 2 x else 0)
  rw [<- he]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, finTwoArrowEquiv,
    trialMass, Fin.prod_univ_two, half_mass]

/-- Any two-trial output containing the zero atom has no generating seed array. -/
theorem zero_atom_joint (x : Fin 2 -> Fin 3) (hx : x 0 = 2) :
    (Fintype.card {seeds : SeedArray 2 1 // sampleArray halfWithZero 3 1 2 half_normalized seeds = x} : Rat) /
      Fintype.card (SeedArray 2 1) = 0 := by
  rw [array_fibre_probability halfWithZero 3 1 2 half_normalized half_nonneg]
  simp [trialMass, Fin.prod_univ_two, hx, half_mass]

theorem concrete_real_event_bridge :
    seedProbability 2 1 (fun seeds =>
      sampleArray halfWithZero 3 1 2 half_normalized seeds 0 =
      sampleArray halfWithZero 3 1 2 half_normalized seeds 1) =
      FiniteConcentration.probability (fun i : Fin 3 => mass halfWithZero 2 i.val) 2
        (fun x => x 0 = x 1) := by
  simpa using sampleArray_probability halfWithZero 3 1 2 half_normalized half_nonneg (fun x => x 0 = x 1)

#print axioms array_fibre_card
#print axioms bit_fibre_probability
#print axioms array_fibre_probability
#print axioms sampleArray_event_law
#print axioms sampleArray_probability
#print axioms half_nonneg
#print axioms half_normalized
#print axioms half_mass
#print axioms two_trial_diagonal
#print axioms zero_atom_joint
#print axioms concrete_real_event_bridge
end PvNP.RealizableHardness.JointSamplingLaw
