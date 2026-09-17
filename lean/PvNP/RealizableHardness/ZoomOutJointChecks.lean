import PvNP.RealizableHardness.ZoomOutJoint
/-! UNCOMPILED: these commands are not kernel evidence. -/
open PvNP.RealizableHardness ZoomOutJoint PosteriorReweighting
open scoped BigOperators

set_option pp.fullNames true in
#check favorable_marginal_lower
set_option pp.fullNames true in
#check ready_joint_success
set_option pp.fullNames true in
#check eventual_joint_success

#print axioms mass_and_not_lower
#print axioms score_threshold
#print axioms agreement_bounds
#print axioms ready_posterior_success
#print axioms favorable_marginal_lower
#print axioms jointSuccess_disintegration
#print axioms ready_joint_success
#print axioms eventual_joint_success

example : mass (fun _ : Unit => (1 : ℚ)) (fun _ => true && !true) = 0 := by
  simp [mass]
example : mass (fun _ : Unit => (1 : ℚ)) (fun _ => true && !false) = 1 := by
  simp [mass]
example : (1 : ℚ)/4 ≤ mass (fun _ : Unit => 1) (fun _ => decide ((1 : ℚ)/4 ≤ 1)) := by
  norm_num [mass]
example : (1 : ℚ)/8 ≤ 1/4 - 2*(1/16) := by norm_num
example : (0 : ℚ) ≤ mass (fun _ : Unit => 1) (fun _ => decide ((0 : ℚ)/4 ≤ 0)) := by
  norm_num [mass]
example : mean (fun _ : Unit => (0 : ℚ)) (fun _ => 1) = 0 := by simp [mean]

example {X : Type*} [Fintype X] (p : X → ℚ) (hp : ∀ x, 0 ≤ p x)
    (b c : X → Bool) : mass p b - mass p c ≤ mass p (fun x => b x && !(c x)) :=
  mass_and_not_lower p hp b c

example {X : Type*} [Fintype X] (p f : X → ℚ) (hp : ∀ x, 0 ≤ p x)
    (hn : ∑ x, p x = 1) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (C : ℚ) (hC : 0 ≤ C) (hm : C/2 ≤ mean p f) :
    C/4 ≤ mass p (fun x => decide (C/4 ≤ f x)) :=
  score_threshold p f hp hn hf C hC hm
