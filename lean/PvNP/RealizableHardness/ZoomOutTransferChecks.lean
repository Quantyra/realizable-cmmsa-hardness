import PvNP.RealizableHardness.ZoomOutTransfer
/- UNCOMPILED: all queries and examples await execution. -/
open PvNP.RealizableHardness
open ZoomOutTransfer PosteriorReweighting ZoomOutPosterior
open scoped BigOperators

#print axioms condition_normalized
#print axioms condition_null
#print axioms condition_sum_le_one
#print axioms gated_zero
#print axioms condition_tv_mul_le
#print axioms score_tv_le
#print axioms condition_score_bounds
#print axioms mixture_event_mass
#print axioms condition_mixture
#print axioms mixture_score
#print axioms retained_event_mass_eq
#print axioms ambient_event_mass_eq
#print axioms deleted_event_eq_normalizer
#print axioms exact_disintegration
#print axioms ambient_codim_dimension
#print axioms total_error_small
#print axioms ready_transfer
#print axioms eventual_transfer
#print axioms conclusion_event
#print axioms conclusion_mass_defect
#print axioms ZoomOutTransfer.conclusion_score_real

example : condition (fun _ : Unit => (0 : ℚ)) (fun _ => true) () = 0 := by
  simp [condition, mass]
example : condition (fun _ : Unit => (1 : ℚ)) (fun _ => false) () = 0 := by
  simp [condition, mass]
example : condition (fun _ : Unit => (1 : ℚ)) (fun _ => true) () = 1 := by
  simp [condition, mass]
example : ∑ x : Unit, condition (fun _ => (0 : ℚ)) (fun _ => true) x = 0 := by
  simp [condition, mass]
example : ∑ x : Unit, condition (fun _ => (1 : ℚ)) (fun _ => true) x = 1 := by
  simp [condition, mass]

example {X : Type*} [Fintype X] (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b : X → Bool)
    (hz : mass p b = 0) (x : X) : (if b x then p x else 0) = 0 := gated_zero p hp b hz x

example {X : Type*} [Fintype X] (p q : X → ℚ) (hq : ∀ x, 0 ≤ q x) (b : X → Bool)
    (hpE : 0 < mass p b) (hqE : 0 < mass q b) :
    mass p b * AdviceExceptions.tv (condition p b) (condition q b) ≤ 2 * AdviceExceptions.tv p q :=
  condition_tv_mul_le p q hq b hpE hqE

example : 8*qdecay 100 1/GaussianNearOne.leading (2*1-0) 0 + qdecay 12 1 < qdecay 10 1 :=
  total_error_small (r := 0) (a := 0) (by omega) (by omega)

example {r h a c : ℕ} (hh : r < h) (hc : c ≤ r) :
    8*qdecay 100 h/GaussianNearOne.leading (2*h-a) c + qdecay 12 h < qdecay 10 h :=
  total_error_small hh hc
