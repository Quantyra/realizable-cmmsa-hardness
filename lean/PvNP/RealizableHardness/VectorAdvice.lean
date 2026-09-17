import PvNP.RealizableHardness.ZoomOutJoint

/-! UNCOMPILED. Uniform vector tuples with explicit failure on dependence.
This is a fixed-length shared-prefix marginal, not a complete prover strategy. -/
namespace PvNP.RealizableHardness.VectorAdvice
open scoped BigOperators
open GrassmannCounting CoveringSpan GrassmannIncidence TripleRestrictionRank
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

section Internal
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] {a : ℕ}

/-- Actual deterministic span on independence; dependence is an explicit failure. -/
def output (v : Fin a → V) : Option (Grass V a) :=
  if h : LinearIndependent (ZMod 2) v then some (spanFrame ⟨v, h⟩) else none

def outputLaw (q : Option (Grass V a)) : ℝ :=
  ∑ v : Fin a → V, uniformArray v * (if output v = q then 1 else 0)

lemma output_none_of_dimension_lt (h : Module.finrank (ZMod 2) V < a) (v : Fin a → V) :
    output v = none := by
  have hv : ¬ LinearIndependent (ZMod 2) v := by
    intro hi
    have hl := (Submodule.span (ZMod 2) (Set.range v)).finrank_le
    rw [finrank_span_eq_card hi, Fintype.card_fin] at hl
    omega
  simp [output, hv]

lemma outputLaw_none : outputLaw (V := V) (a := a) none = failureFraction V a := by
  unfold outputLaw uniformArray
  rw [← Finset.mul_sum, split_arrays]
  have hi : (∑ v : Frame V a, if output v.val = none then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [output, v.property]
  have hb : (∑ v : BadArray V a, if output v.val = none then (1 : ℝ) else 0) =
      Fintype.card (BadArray V a) := by
    have he (v : BadArray V a) : (if output v.val = none then (1 : ℝ) else 0) = 1 := by
      simp [output, v.property]
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hi, hb, zero_add]
  simp [failureFraction, div_eq_mul_inv, mul_comm]

/-- The successful mass is counted by the accepted constant-size frame fibres. -/
lemma outputLaw_some (ha : a ≤ Module.finrank (ZMod 2) V) (Q : Grass V a) :
    outputLaw (some Q) = (1-failureFraction V a) * uniformGrass Q := by
  have hn : (Fintype.card (Fin a → V) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := Fin a → V)))
  have hg : (Fintype.card (Grass V a) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (grass_card_pos ha))
  have hc := array_card_split (V := V) ha
  unfold outputLaw uniformArray
  rw [← Finset.mul_sum, split_arrays]
  have hi : (∑ v : Frame V a, if output v.val = some Q then (1 : ℝ) else 0) =
      (frameProduct a a : ℝ) := by
    have he (v : Frame V a) : (if output v.val = some Q then (1 : ℝ) else 0) =
        if spanFrame v = Q then 1 else 0 := by
      simp [output, v.property]
      rfl
    simp only [he]
    simpa using sum_over_frames (V := V) (fun R => if R = Q then (1 : ℝ) else 0)
  have hb : (∑ v : BadArray V a, if output v.val = some Q then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [output, v.property]
  rw [hi, hb, add_zero]
  unfold failureFraction uniformGrass
  field_simp
  nlinarith [hc]

lemma success_pos (ha : a ≤ Module.finrank (ZMod 2) V) :
    0 < 1-failureFraction V a := by
  have hc := array_card_split (V := V) ha
  have hg : (0 : ℝ) < Fintype.card (Grass V a) := by exact_mod_cast grass_card_pos ha
  have hf : (0 : ℝ) < frameProduct a a := by exact_mod_cast frameProduct_self_pos a
  have hn : (0 : ℝ) < Fintype.card (Fin a → V) := by
    exact_mod_cast (Fintype.card_pos (α := Fin a → V))
  unfold failureFraction
  apply sub_pos.mpr
  apply (div_lt_one hn).mpr
  nlinarith [mul_pos hg hf]

/-- Conditioning the actual tuple output on success is exactly uniform span. -/
theorem conditional_output_uniform (ha : a ≤ Module.finrank (ZMod 2) V) (Q : Grass V a) :
    outputLaw (some Q) / (1-failureFraction V a) = uniformGrass Q := by
  rw [outputLaw_some ha]
  exact mul_div_cancel_left₀ _ (ne_of_gt (success_pos ha))

def score (g : Grass V a → ℝ) : ℝ :=
  ∑ v : Fin a → V, uniformArray v * (output v).elim 0 g

lemma score_eq (ha : a ≤ Module.finrank (ZMod 2) V) (g : Grass V a → ℝ) :
    score g = (1-failureFraction V a) * ∑ Q, uniformGrass Q * g Q := by
  have he (v : Fin a → V) : (output v).elim 0 g =
      ∑ Q : Grass V a, (if output v = some Q then (1 : ℝ) else 0) * g Q := by
    cases ho : output v <;> simp [ho]
  unfold score
  simp only [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hatom (Q : Grass V a) :
      (∑ v : Fin a → V, uniformArray v * ((if output v = some Q then (1 : ℝ) else 0) * g Q)) =
        outputLaw (some Q) * g Q := by simp [outputLaw, Finset.sum_mul, mul_assoc]
  simp only [hatom, outputLaw_some ha]
  apply Finset.sum_congr rfl
  intro Q _
  ring

lemma failure_zero : failureFraction V 0 = 0 := by
  rw [failureFraction_eq (Nat.zero_le _)]
  simp [frameProduct]

lemma failure_le_geometric_sum (ha : a ≤ Module.finrank (ZMod 2) V) :
    failureFraction V a ≤ ∑ i ∈ Finset.range a,
      (2 : ℝ)^i / (2 : ℝ)^Module.finrank (ZMod 2) V := by
  have hs : (∑ i ∈ Finset.range a, (2 : ℝ)^i) = (2 : ℝ)^a-1 := by
    clear ha
    induction a with
    | zero => simp
    | succ a ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [← Finset.sum_div, hs]
  exact failureFraction_le ha

end Internal

section Subspace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] {a : ℕ}

lemma uniform_include_score (W : Submodule (ZMod 2) V) (g : Grass V a → ℝ) :
    (∑ R : Grass W a, uniformGrass R * g (includeSubspace W R).val) =
      ∑ Q : Grass V a, subspaceLaw W Q * g Q := by
  have hi (R : Grass W a) : g (includeSubspace W R).val =
      ∑ Q : Grass V a, (if (includeSubspace W R).val = Q then (1 : ℝ) else 0) * g Q := by simp
  simp only [uniformGrass, hi, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q _
  have he : (∑ R : Grass W a,
      (Fintype.card (Grass W a) : ℝ)⁻¹ * ((if (includeSubspace W R).val = Q then 1 else 0) * g Q)) =
      (Fintype.card (Grass W a) : ℝ)⁻¹ *
        (∑ R : Grass W a, if (includeSubspace W R).val = Q then (1 : ℝ) else 0) * g Q := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro R _
    ring
  rw [he, sum_include_indicator]
  by_cases hQ : Q.val ≤ W <;> simp [subspaceLaw, hQ]

def subspaceScore (W : Submodule (ZMod 2) V) (g : Grass V a → ℝ) : ℝ :=
  score (fun R : Grass W a => g (includeSubspace W R).val)

theorem subspaceScore_eq (W : Submodule (ZMod 2) V)
    (ha : a ≤ Module.finrank (ZMod 2) W) (g : Grass V a → ℝ) :
    subspaceScore W g = (1-failureFraction W a) * ∑ Q, subspaceLaw W Q * g Q := by
  rw [subspaceScore, score_eq ha, uniform_include_score]

end Subspace

variable {J a r : ℕ}

/-- Written as a quotient to avoid truncated natural subtraction in r-J. -/
def error (r J : ℕ) : ℝ := (2 : ℝ)^r / (2 : ℝ)^J

lemma retained_error (s : Draw J) (ha : a ≤ r) (hr : r ≤ J) :
    failureFraction (retained s) a ≤ error r J := by
  apply (retained_failure_le s (ha.trans hr)).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  linarith

lemma retained_score_eq (s : Draw J) (ha : a ≤ J) (g : Advice J a → ℝ) :
    subspaceScore (retained s) g =
      (1-failureFraction (retained s) a) * ∑ Q, (kernel s Q : ℝ) * g Q := by
  have he := subspaceScore_eq (retained s) (ha.trans (GrassmannIncidence.retained_finrank_lower s)) g
  apply he.trans
  congr 1
  apply Finset.sum_congr rfl
  intro Q _
  exact congrArg (fun t : ℝ => t * g Q) (subspaceLaw_retained s Q)

/-- Joint score retains the same draw s in the score; dependence fails, not resamples. -/
def actualJointScore (β : ℚ) (g : Draw J → Advice J a → ℝ) : ℝ :=
  ∑ s : Draw J, (prior β s : ℝ) * subspaceScore (retained s) (g s)

def idealJointScore (β : ℚ) (g : Draw J → Advice J a → ℝ) : ℝ :=
  ∑ s : Draw J, (prior β s : ℝ) * ∑ Q : Advice J a, (kernel s Q : ℝ) * g s Q

theorem joint_score_loss (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ r) (hr : r ≤ J) (g : Draw J → Advice J a → ℝ)
    (hg : ∀ s Q, 0 ≤ g s Q ∧ g s Q ≤ 1) :
    0 ≤ idealJointScore β g - actualJointScore β g ∧
      idealJointScore β g - actualJointScore β g ≤ error r J := by
  let G : Draw J → ℝ := fun s => ∑ Q : Advice J a, (kernel s Q : ℝ) * g s Q
  have hG (s : Draw J) : 0 ≤ G s ∧ G s ≤ 1 := by
    have hn : (∑ Q : Advice J a, (kernel s Q : ℝ)) = 1 := by
      exact_mod_cast kernel_normalized s (ha.trans hr)
    constructor
    · exact Finset.sum_nonneg fun Q _ => mul_nonneg (by exact_mod_cast kernel_nonneg s Q) (hg s Q).1
    · apply le_trans (Finset.sum_le_sum fun Q _ =>
        mul_le_of_le_one_right (by exact_mod_cast kernel_nonneg s Q) (hg s Q).2)
      exact hn.le
  have hp (s : Draw J) : (0 : ℝ) ≤ prior β s := by exact_mod_cast drawMass_nonneg β hβ hβ1 s
  have hn : (∑ s : Draw J, (prior β s : ℝ)) = 1 := by exact_mod_cast prior_normalized (J := J) β
  have he : idealJointScore β g - actualJointScore β g =
      ∑ s : Draw J, (prior β s : ℝ) * (failureFraction (retained s) a * G s) := by
    unfold idealJointScore actualJointScore
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [retained_score_eq s (ha.trans hr)]
    dsimp [G]
    ring
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun s _ => mul_nonneg (hp s)
      (mul_nonneg failureFraction_nonneg (hG s).1)
  · calc
      _ ≤ ∑ s : Draw J, (prior β s : ℝ) * error r J := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (hp s)
        exact (mul_le_of_le_one_right failureFraction_nonneg (hG s).2).trans (retained_error s ha hr)
      _ = error r J := by rw [← Finset.sum_mul, hn, one_mul]

lemma ideal_event_eq_joint (β : ℚ) (E : Draw J → Advice J a → Bool) :
    idealJointScore β (fun s Q => if E s Q then 1 else 0) =
      ((∑ s : Draw J, ∑ Q : Advice J a,
        if E s Q then joint β s Q else 0 : ℚ) : ℝ) := by
  unfold idealJointScore
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro Q _
  cases he : E s Q <;> simp [he, joint]

/-- Charge vector dependence against the very decoder event in ZoomOutJoint. -/
theorem decoder_event_transfer {A h a r : ℕ} (ha : a ≤ r) (hr : r ≤ SamplerParameters.blocks A h)
    (F : Advice (SamplerParameters.blocks A h) a → Bool)
    (W : Advice (SamplerParameters.blocks A h) a →
      Submodule (ZMod 2) (Vector (SamplerParameters.blocks A h)))
    (f : Advice (SamplerParameters.blocks A h) a → Advice (SamplerParameters.blocks A h) (2*h) → ℚ)
    (C : ℚ) :
    (ZoomOutJoint.jointSuccess F W f C : ℝ) - error r (SamplerParameters.blocks A h) ≤
      actualJointScore (SamplerParameters.beta A h) (fun s Q =>
        if ZoomOutJoint.favorable F Q && ZoomOutJoint.succeeds Q (W Q) (f Q) C s then 1 else 0) := by
  let E := fun s Q => ZoomOutJoint.favorable F Q && ZoomOutJoint.succeeds Q (W Q) (f Q) C s
  have hb : ∀ s Q, 0 ≤ (if E s Q then (1 : ℝ) else 0) ∧
      (if E s Q then (1 : ℝ) else 0) ≤ 1 := by
    intro s Q
    cases E s Q <;> norm_num
  have hl := (joint_score_loss (SamplerParameters.beta A h)
    (SamplerParameters.beta_nonneg A h) (SamplerParameters.beta_le_one A h)
    ha hr (fun s Q => if E s Q then 1 else 0) hb).2
  rw [ideal_event_eq_joint] at hl
  change (ZoomOutJoint.jointSuccess F W f C : ℝ) - _ ≤ _ at hl
  linarith

end
end PvNP.RealizableHardness.VectorAdvice
