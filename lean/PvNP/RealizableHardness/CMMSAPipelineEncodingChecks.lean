import PvNP.RealizableHardness.CMMSAPipelineEncoding
/-! Uncompiled semantic bridge checks. -/
open PvNP.RealizableHardness CMMSACodec CMMSAEncoding CMMSAPipelineEncoding

#print axioms indexed_cost
#print axioms indexed_satisfaction
#print axioms weight_equiv
#print axioms outputData_valid
#print axioms outputInstance_data
#print axioms decode_outputBits
#print axioms output_cost
#print axioms output_satisfaction
#print axioms average_one_iff
#print axioms output_yes_iff
#print axioms output_no_iff
#print axioms yes_preserved
#print axioms no_preserved
#print axioms seeded_leaf_bound
#print axioms seeded_record
#print axioms seeded_yes_iff
#print axioms seeded_no_iff

example (f : Fin 2 → Bool) : 1 ≤ average f ↔ ∀ i, f i = true := average_one_iff f
example (w : Fin 2 → Rat) (x : Fin 2 → Bool) : weight w x = weight w x :=
  weight_equiv (Equiv.refl _) w x
example {N M L : Nat} {w : Fin N → Rat} (a : FiniteRepairRoundingPipeline.Parameters w)
    (F : Fin M → Formula (Fin N)) (hM : 0 < M)
    (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) :
    Valid L (outputData a F) := outputData_valid a F hM hF
example {N M L : Nat} {w : Fin N → Rat} (a : FiniteRepairRoundingPipeline.Parameters w)
    (F : Fin M → Formula (Fin N)) (hM : 0 < M)
    (hF : ∀ i, Formula.leaves (F i)+1 ≤ L) :
    (decode L (outputBits a F hM hF)).map Instance.data = some (outputData a F) :=
  decode_outputBits a F hM hF
