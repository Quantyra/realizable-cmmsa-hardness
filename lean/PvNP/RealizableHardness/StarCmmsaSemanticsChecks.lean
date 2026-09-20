import PvNP.RealizableHardness.StarCmmsaSemantics

namespace PvNP.RealizableHardness.StarCmmsaSemanticsChecks

open scoped BigOperators
open PvNP.RealizableHardness.StarListDecoding
open PvNP.RealizableHardness.StarFormulaInterface
open PvNP.RealizableHardness.StarCmmsaSemantics

noncomputable section
attribute [local instance] Classical.propDecidable

private def repeated : Star Bool (fun _ => Bool) 2 where
  center := false
  leaf := fun _ => true
  projection := fun _ a => a
  separated := by intro i; decide

example : repeated.leaf 0 = repeated.leaf 1 := rfl

example : repeated.listWitness (fun _ => {false}) := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · intro i
    rfl
  · intro j
    simp

private def emptyFibre : Star (Fin 3) (fun _ => Bool) 2 where
  center := 0
  leaf := fun i => i.succ
  projection := fun i _ => if i = 0 then false else true
  separated := by
    intro i
    fin_cases i <;> decide

private theorem emptyFibre_no_accepts :
    ¬ ∃ l : (v : Fin 3) → Bool, emptyFibre.accepts l := by
  rintro ⟨l, hl⟩
  have h0 := hl (0 : Fin 2)
  have h1 := hl (1 : Fin 2)
  cases hv : l 0 <;> simp [emptyFibre, hv] at h0 h1

example : compile emptyFibre = none := by
  exact (compile_eq_none_iff emptyFibre).mpr emptyFibre_no_accepts

example : evalOpt (fun _ => false) (compile emptyFibre) = false := by
  rw [show compile emptyFibre = none from
    (compile_eq_none_iff emptyFibre).mpr emptyFibre_no_accepts]
  rfl

example : compiledSatisfaction (fun _ : Unit => (1 : ℝ))
    (fun _ => emptyFibre) (fun _ => false) = 0 := by
  simp [compiledSatisfaction, eventMass,
    (compile_eq_none_iff emptyFibre).mpr emptyFibre_no_accepts, evalOpt]

example : alphabetMass (fun _ : Unit => (1 : ℝ)) (fun _ => repeated) = (2 : ℝ) := by
  exact constantAlphabet_alphabetMass_eq
    (fun _ : Unit => (1 : ℝ)) (by simp)
    (fun _ => repeated) (R := 2) (by intro v; simp)

#check starWeight
#check starBudget
#check assignmentCost
#check compiledSatisfaction
#check starWeight_sum
#check assignmentCost_eq_selectedWeight
#check compiledSatisfaction_eq_witnessMass
#check constantAlphabet_alphabetMass_eq
#check compiledSatisfaction_le_three_quarters

#print axioms starWeight_sum
#print axioms assignmentCost_eq_selectedWeight
#print axioms compiledSatisfaction_eq_witnessMass
#print axioms constantAlphabet_alphabetMass_eq
#print axioms compiledSatisfaction_le_three_quarters

end
end PvNP.RealizableHardness.StarCmmsaSemanticsChecks
