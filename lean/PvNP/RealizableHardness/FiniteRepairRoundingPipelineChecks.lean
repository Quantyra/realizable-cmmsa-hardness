import PvNP.RealizableHardness.FiniteRepairRoundingPipeline

namespace PvNP.RealizableHardness.FiniteRepairRoundingPipeline

def unitWeights (_ : Unit) : Rat := 1
def unitFormula (_ : Unit) : Formula Unit := .var ()

def yesParameters : Parameters unitWeights where
  s := 1
  eps := 0
  gam := 1 / 4
  sig := 8
  weights_pos := by intro v; norm_num [unitWeights]
  weights_sum := by simp [unitWeights]
  s_pos := by norm_num
  s_le_one := by norm_num
  eps_nonneg := by norm_num
  gam_pos := by norm_num
  gam_lt_half := by norm_num
  sig_ge := by norm_num
  small := by norm_num

def noParameters : Parameters unitWeights where
  s := 1 / 32
  eps := 0
  gam := 1 / 4
  sig := 8
  weights_pos := by intro v; norm_num [unitWeights]
  weights_sum := by simp [unitWeights]
  s_pos := by norm_num
  s_le_one := by norm_num
  eps_nonneg := by norm_num
  gam_pos := by norm_num
  gam_lt_half := by norm_num
  sig_ge := by norm_num
  small := by norm_num

theorem genuine_yes_example :
    ∃ y : Unit ⊕ Unit -> Bool,
      weight (outputWeights yesParameters) y <= outputBudget (I := Unit) yesParameters ∧
      forall i, Formula.eval y (outputFormula unitFormula i) = true := by
  apply yes_preserved yesParameters unitFormula (fun _ => true)
  · norm_num [weight, unitWeights, yesParameters]
  · norm_num [average, Formula.eval, unitFormula, yesParameters]

theorem genuine_no_input : forall x : Unit -> Bool,
    weight unitWeights x <= (noParameters.sig : Rat) * noParameters.s ->
      average (fun i => Formula.eval x (unitFormula i)) < noParameters.gam := by
  intro x hx
  cases he : x ()
  · norm_num [average, Formula.eval, unitFormula, noParameters, he]
  · norm_num [weight, unitWeights, noParameters, he] at hx

theorem genuine_no_example (y : Unit ⊕ Unit -> Bool)
    (hy : weight (outputWeights noParameters) y <=
      (gap noParameters : Rat) * outputBudget (I := Unit) noParameters) :
    average (fun i => Formula.eval y (outputFormula unitFormula i)) < 2 * noParameters.gam :=
  no_preserved noParameters unitFormula genuine_no_input y hy

theorem concrete_denominator_bound : outputDenominator (I := Unit) noParameters <= 3074 := by
  have h := denominator_bound (I := Unit) noParameters 32 32 (by norm_num [noParameters])
    (by norm_num [noParameters])
  simpa using h

theorem concrete_repaired_leaf_count : Formula.leaves (outputFormula unitFormula ()) = 2 := by
  simp [unitFormula, Formula.leaves]

#print axioms lam_pos
#print axioms eps_le_one
#print axioms budget_pos
#print axioms budget_le_one
#print axioms weights_pos
#print axioms weights_sum
#print axioms output_valid
#print axioms yes_preserved
#print axioms no_preserved
#print axioms output_leaves
#print axioms reciprocal_budget
#print axioms denominator_bound
#print axioms output_common_denominator
#print axioms genuine_yes_example
#print axioms genuine_no_input
#print axioms genuine_no_example
#print axioms concrete_denominator_bound
#print axioms concrete_repaired_leaf_count
end PvNP.RealizableHardness.FiniteRepairRoundingPipeline
