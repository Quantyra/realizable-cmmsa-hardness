import PvNP.RealizableHardness.ActualVisibleJointSuccess
import PvNP.RealizableHardness.VectorAdvice

/-! Charge actual vector dependence against the literal visible success
event, retaining the original draw and its completion-dependent exclusions.
This is not a source-game identification. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVisibleVectorAdvice

open PvNP.RealizableHardness
open ActualVisibleJointSuccess TripleRestrictionRank GrassmannIncidence
open SamplerParameters VectorAdvice

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual independent-vector score of the new visible event loses at
most the proved rank-dependence error. No resampling or new conditioning. -/
theorem visible_joint_event_vector_transfer {A h a r : Nat}
    (ha : a ≤ r) (hr : r ≤ blocks A h)
    (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (g : Advice (blocks A h) a → Draw (blocks A h) → Rat) (C : Rat) :
    (jointVisibleSuccess F W H g C : Real) - error r (blocks A h) ≤
      actualJointScore (beta A h) (fun s Q =>
        if goodFavorable F H Q && visibleEvent Q (W Q) H (g Q) C s then 1 else 0) := by
  let E := fun s Q =>
    goodFavorable F H Q && visibleEvent Q (W Q) H (g Q) C s
  have hbound : ∀ s Q, 0 ≤ (if E s Q then (1 : Real) else 0) ∧
      (if E s Q then (1 : Real) else 0) ≤ 1 := by
    intro s Q
    cases E s Q <;> norm_num
  have hloss := (joint_score_loss (beta A h) (beta_nonneg A h) (beta_le_one A h)
    ha hr (fun s Q => if E s Q then 1 else 0) hbound).2
  rw [ideal_event_eq_joint] at hloss
  change (jointVisibleSuccess F W H g C : Real) -
    actualJointScore (beta A h) (fun s Q => if E s Q then 1 else 0) ≤
      error r (blocks A h) at hloss
  change (jointVisibleSuccess F W H g C : Real) - error r (blocks A h) ≤
    actualJointScore (beta A h) (fun s Q => if E s Q then 1 else 0)
  linarith

end
end PvNP.RealizableHardness.ActualVisibleVectorAdvice
