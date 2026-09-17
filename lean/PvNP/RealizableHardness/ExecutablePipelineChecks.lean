import PvNP.RealizableHardness.ExecutablePipeline
/-! Uncompiled checks for the complete executable output constructor. -/
open PvNP.RealizableHardness ExecutablePipeline
#print axioms draws_eq
#print axioms repaired_eval
#print axioms repaired_leaves
#print axioms data_count
#print axioms read_tree
#print axioms record_congr
#print axioms data_eq
#print axioms draws_leaf_bound
#print axioms data_valid
#print axioms formula_wire_bound
#print axioms full_wire_bound
#print axioms checkedBits_reject
#print axioms instanceOf_data
#print axioms decode_bits
#print axioms decode_seeded_data
#print axioms checkedBits_valid

example (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray 0 b) :
    (data ws t b 0 q seeds).formulas = [] := by simp [data]

example {N : Nat} (t : FiniteSourceSampler.Table N) (b : Nat)
    (seeds : JointSamplingLaw.SeedArray 2 b) :
    Formula.leaves (repaired t b 2 seeds 0) = Formula.leaves (draws t b 2 seeds 0)+1 :=
  repaired_leaves t b 2 seeds 0

example (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b) :
    (data ws t b M q seeds).weights.length = ws.length+M := by
  simp [data]

example {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L) :
    (CMMSACodec.decode L (bits ws t b M (ExecutableRounding.inputOf p) seeds)).map
      CMMSACodec.Instance.data = some (CMMSAPipelineEncoding.outputData p
        (SamplingFormulaPromises.fromSeeds (FiniteSourceSampler.probability t)
          t.rows.length b M (FiniteSourceSampler.cumulative_endpoint t)
          (FiniteSourceSampler.formula t) seeds)) := decode_bits ws t b M p seeds hM hF
