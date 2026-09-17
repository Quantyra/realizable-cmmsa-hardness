import PvNP.RealizableHardness.StarListDecoding

namespace PvNP.RealizableHardness.StarListDecoding
open scoped BigOperators

private def repeated : Star Bool (fun _ => Bool) 2 where
  center := false
  leaf := fun _ => true
  projection := fun _ a => a
  separated := by intro i; decide

private def conflicting : Star Bool (fun _ => Bool) 2 where
  center := false
  leaf := fun _ => true
  projection := fun i a => if i = 0 then a else !a
  separated := by intro i; decide

/-- The same leaf is permitted in both slots. -/
example : repeated.leaf 0 = repeated.leaf 1 := rfl

example : repeated.listWitness (fun _ => {false}) := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · intro i; rfl
  · intro j; simp

/-- Nonempty lists need not yield a coherent repeated-vertex witness. -/
example : ¬ conflicting.listWitness (fun _ => Finset.univ) := by
  rintro ⟨l, h, _⟩
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  simp [conflicting] at h0 h1
  cases ht : l true <;> simp_all

example : ¬ repeated.listWitness (fun _ => ∅) := by
  rintro ⟨l, _, h⟩
  simpa using h (0 : Fin 3)

/-- A zero-mass occurrence is retained but contributes exactly zero. -/
example : score (fun _ : Bool => (0 : ℝ)) (fun _ => repeated) (fun _ => false) = 0 := by
  classical
  simp [score, eventMass]

#print axioms Star.accepts_of_agree
#print axioms coordMass_sum
#print axioms labelMass_sum
#print axioms cylinder_factorization
#print axioms cylinder_pinned
#print axioms edgeProbability_ge_distinct
#print axioms slot_product_le
#print axioms edgeProbability_good
#print axioms occurrenceWeight_sum
#print axioms alphabetMass_ge_one
#print axioms selectedWeight_budget_iff
#print axioms mean_slotSum
#print axioms bad_mass_le
#print axioms good_mass_ge
#print axioms exists_decoding
#print axioms exists_decoding_of_selectedWeight
#print axioms witness_mass_le_three_quarters
#check exists_decoding
#check selectedWeight_budget_iff
#check witness_mass_le_three_quarters

end PvNP.RealizableHardness.StarListDecoding
