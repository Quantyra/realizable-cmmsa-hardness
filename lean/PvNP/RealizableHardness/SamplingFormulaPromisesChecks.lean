import PvNP.RealizableHardness.SamplingFormulaPromises

/-! Scoped proof profiles, duplicate positions and zero-trial identity examples. -/
namespace PvNP.RealizableHardness.SamplingFormulaPromisesChecks
open SamplingFormulaPromises

theorem duplicate_positions :
    sampled (fun _ => Formula.var (0 : Fin 1)) (fun _ : Fin 2 => (0 : Fin 1)) 0 =
      sampled (fun _ => Formula.var (0 : Fin 1)) (fun _ : Fin 2 => (0 : Fin 1)) 1 := rfl

theorem duplicate_empirical (x : Fin 1 → Bool) :
    FiniteConcentration.empirical
      (fun i : Fin 1 => events (fun _ => Formula.var (0 : Fin 1)) x i.val) 2
      (fun _ => (0 : Fin 1)) =
    (average (fun _ : Fin 2 => x 0) : Real) :=
  empirical_eq_average (fun _ => Formula.var (0 : Fin 1)) (fun _ => (0 : Fin 1)) x

theorem empty_trials (F : Nat → Formula (Fin 1)) (x : Fin 1 → Bool)
    (draws : Fin 0 → Fin 0) :
    FiniteConcentration.empirical (fun i : Fin 0 => events F x i.val) 0 draws =
      (average (fun i => Formula.eval x (sampled F draws i)) : Real) :=
  empirical_eq_average F draws x

#print axioms SamplingFormulaPromises.empirical_eq_average
#print axioms SamplingFormulaPromises.good_yes_average
#print axioms SamplingFormulaPromises.good_no_average
#print axioms SamplingFormulaPromises.parameter_margin
#print axioms SamplingFormulaPromises.good_yes_output
#print axioms SamplingFormulaPromises.good_no_output
#print axioms SamplingFormulaPromises.fromSeeds_eval
#print axioms SamplingFormulaPromises.output_leaves
#print axioms SamplingFormulaPromises.seedProbability_mono
#print axioms SamplingFormulaPromises.computed_event_probability
#print axioms SamplingFormulaPromises.computed_yes_probability
#print axioms SamplingFormulaPromises.computed_no_probability
#print axioms duplicate_positions
#print axioms duplicate_empirical
#print axioms empty_trials
end PvNP.RealizableHardness.SamplingFormulaPromisesChecks
