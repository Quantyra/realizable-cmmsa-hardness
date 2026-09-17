import PvNP.RealizableHardness.VectorAdvice
/-! UNCOMPILED; no axiom or example result is claimed. -/
open PvNP.RealizableHardness VectorAdvice CoveringSpan GrassmannCounting
open scoped BigOperators

#print axioms output_none_of_dimension_lt
#print axioms outputLaw_none
#print axioms outputLaw_some
#print axioms success_pos
#print axioms conditional_output_uniform
#print axioms score_eq
#print axioms failure_zero
#print axioms failure_le_geometric_sum
#print axioms uniform_include_score
#print axioms subspaceScore_eq
#print axioms retained_error
#print axioms retained_score_eq
#print axioms joint_score_loss
#print axioms ideal_event_eq_joint
#print axioms decoder_event_transfer

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] :
    failureFraction V 0 = 0 := failure_zero

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] {a : ℕ}
    (h : Module.finrank (ZMod 2) V < a) (v : Fin a → V) : output v = none :=
  output_none_of_dimension_lt h v

example : error 0 0 = 1 := by norm_num [error]
example : error 1 3 = (1/4 : ℝ) := by norm_num [error]
example (r : ℕ) : 0 ≤ error r r := by unfold error; positivity

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] {a : ℕ}
    (ha : a ≤ Module.finrank (ZMod 2) V) (Q : Grass V a) :
    outputLaw (some Q) / (1-failureFraction V a) = uniformGrass Q :=
  conditional_output_uniform ha Q

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] {a : ℕ} :
    score (fun _ : Grass V a => (0 : ℝ)) = 0 := by
  unfold score
  apply Finset.sum_eq_zero
  intro v _
  cases output v <;> simp
