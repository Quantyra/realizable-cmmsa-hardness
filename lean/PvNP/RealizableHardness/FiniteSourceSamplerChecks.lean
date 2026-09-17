import PvNP.RealizableHardness.FiniteSourceSampler
/-! Uncompiled boundary examples. -/
open PvNP.RealizableHardness FiniteSourceSampler

#print axioms readTable_valid
#print axioms readTable_invalid
#print axioms probability_at
#print axioms formula_at
#print axioms probability_outside
#print axioms probability_nonneg
#print axioms cumulative_endpoint
#print axioms cumulative_prefix
#print axioms select_interval
#print axioms select_not_zero_mass
#print axioms selectBits_eq
#print axioms selectArray_eq
#print axioms selected_eq_fromSeeds
#print axioms selected_length
#print axioms selectRaw_invalid
#print axioms selectRaw_ofFn

example : readTable ([] : List (Row 1)) = none := by
  apply readTable_invalid
  simp [ValidRows]
example {N : Nat} (t : Table N) : probability t t.rows.length = 0 :=
  probability_outside t _ le_rfl
example {N : Nat} (t : Table N) : FiniteSampling.cumulative (probability t) t.rows.length = 1 :=
  cumulative_endpoint t
example {N : Nat} (t : Table N) (b : Nat) (seeds : JointSamplingLaw.SeedArray 0 b) :
    selected t b 0 seeds = [] := by simp [selected]
example {N : Nat} (t : Table N) : selectRaw t 0 [0] = none :=
  selectRaw_invalid t 0 [0] (by decide)
example {N : Nat} (t : Table N) (bits : Fin 0 → Fin 2) :
    selectRaw t 0 [] = some (selectBits t 0 bits) := by
  simpa using selectRaw_ofFn t 0 bits
example {N : Nat} (t : Table N) (D : Nat) (r : Fin D) (i : Fin t.rows.length)
    (hz : (t.rows.get i).1 = 0) : select t D r ≠ i := select_not_zero_mass t D r i hz
example {N : Nat} (t : Table N) (b : Nat) (bits : Fin b → Fin 2) :
    (selected t b 2 (fun _ => bits)).length = 2 := selected_length t b 2 _
