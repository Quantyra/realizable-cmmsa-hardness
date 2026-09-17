import PvNP.RealizableHardness.SeedEncoding

namespace PvNP.RealizableHardness.SeedEncoding
open JointSamplingLaw

theorem zero_trials_inverse (b : Nat) (seeds : SeedArray 0 b) :
    unflatten 0 b (flatten 0 b seeds) = seeds := unflatten_flatten 0 b seeds

theorem zero_width_inverse (M : Nat) (seeds : SeedArray M 0) :
    unflatten M 0 (flatten M 0 seeds) = seeds := unflatten_flatten M 0 seeds

theorem zero_trials_flat_inverse (b : Nat) (bits : FlatSeed (0 * b)) :
    flatten 0 b (unflatten 0 b bits) = bits := flatten_unflatten 0 b bits

theorem zero_width_flat_inverse (M : Nat) (bits : FlatSeed (M * 0)) :
    flatten M 0 (unflatten M 0 bits) = bits := flatten_unflatten M 0 bits

theorem empty_seed_card : Fintype.card (FlatSeed 0) = 1 := by simp [FlatSeed]

def alternatingBlocks : SeedArray 2 3 :=
  fun i j => finTwoEquiv.symm ((i.val + j.val) % 2 == 1)

/-- The two rows occupy consecutive addresses, and Fin 2 digit 0 maps to false. -/
theorem row_major_example :
    List.ofFn (flatten 2 3 alternatingBlocks) =
      [false, true, false, true, false, true] := by
  norm_num [List.ofFn_succ, flatten, alternatingBlocks, finTwoEquiv,
    finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem padding_example (x : FlatSeed 3) :
    Fintype.card {bits : FlatSeed (3 + 4) // takePrefix 3 4 bits = x} = 16 := by
  rw [prefix_fibre_card]
  norm_num

theorem no_padding_example (n : Nat) (x : FlatSeed n) :
    Fintype.card {bits : FlatSeed (n + 0) // takePrefix n 0 bits = x} = 1 := by
  rw [prefix_fibre_card]
  rfl

theorem empty_prefix_example (k : Nat) (x : FlatSeed 0) :
    Fintype.card {bits : FlatSeed (0 + k) // takePrefix 0 k bits = x} = 2 ^ k :=
  prefix_fibre_card 0 k x

/-- A nonrectangular event is transferred without coordinate independence hypotheses. -/
theorem diagonal_padded_law (p : Nat -> Rat) (S b k : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (hp : forall j, 0 <= p j) :
    uniformProbability (fun bits : FlatSeed (2 * b + k) =>
      sampleFlat p S b 2 hn (takePrefix (2 * b) k bits) 0 =
        sampleFlat p S b 2 hn (takePrefix (2 * b) k bits) 1) =
      FiniteConcentration.probability
        (fun i : Fin S => FiniteSampling.mass p (2 ^ b) i.val) 2
        (fun x => x 0 = x 1) :=
  padded_sampleFlat_probability p S b 2 k hn hp (fun x => x 0 = x 1)

#eval List.ofFn (flatten 2 3 alternatingBlocks)
#eval List.ofFn (joinBits 2 1 ((fun _ => false), (fun _ => true)))

#print axioms unflatten_flatten
#print axioms flatten_unflatten
#print axioms split_join
#print axioms join_split
#print axioms event_card_equiv
#print axioms uniformProbability_equiv
#print axioms uniformProbability_eq_sum
#print axioms seedProbability_eq_uniform
#print axioms flat_event_card
#print axioms flat_probability
#print axioms sampleFlat_probability
#print axioms prefix_fibre_card
#print axioms prefix_event_card
#print axioms prefix_probability
#print axioms padded_sampleFlat_probability
#print axioms zero_trials_inverse
#print axioms zero_width_inverse
#print axioms zero_trials_flat_inverse
#print axioms zero_width_flat_inverse
#print axioms empty_seed_card
#print axioms row_major_example
#print axioms padding_example
#print axioms no_padding_example
#print axioms empty_prefix_example
#print axioms diagonal_padded_law

end PvNP.RealizableHardness.SeedEncoding
