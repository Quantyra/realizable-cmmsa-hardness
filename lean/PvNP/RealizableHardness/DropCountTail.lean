/- UNCOMPILED source draft. No build, axiom audit or independent acceptance yet. -/
import PvNP.RealizableHardness.GrassmannIncidence
import PvNP.RealizableHardness.TripleRestrictionDimension
import PvNP.RealizableHardness.FiniteConcentration

/-! Exponential moments and Chernoff tails for the actual independent triple draw.
No binomial-law premise, supplied moment bound, or posterior independence is used. -/
namespace PvNP.RealizableHardness.DropCountTail
open scoped BigOperators
open TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence

noncomputable section
attribute [local instance] Classical.propDecidable

def dropped (b : BlockChoice) : ℕ := if b ≠ none then 1 else 0

lemma dropCount_eq_sum (d : Draw J) : dropCount d = ∑ j, dropped (d j) :=
  dropCount_sum d

lemma dropCount_cast (d : Draw J) :
    (dropCount d : ℝ) = ∑ j : Fin J, (dropped (d j) : ℝ) := by
  rw [dropCount_eq_sum, Nat.cast_sum]

/-- Rational event mass for the actual draw, cast once into the reals. -/
def tail (β : ℚ) (J T : ℕ) : ℝ :=
  (TripleRestrictionRank.probability β (fun d : Draw J => T < dropCount d) : ℝ)

lemma tail_sum (β : ℚ) (J T : ℕ) :
    tail β J T = ∑ d : Draw J, if T < dropCount d then (prior β d : ℝ) else 0 := by
  simp only [tail, TripleRestrictionRank.probability, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : T < dropCount d <;> simp [hd, prior]

lemma tail_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J T : ℕ) :
    0 ≤ tail β J T := by
  unfold tail
  exact_mod_cast TripleRestrictionRank.probability_nonneg β hβ hβ1
    (fun d : Draw J => T < dropCount d)

lemma tail_le_one (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J T : ℕ) :
    tail β J T ≤ 1 := by
  have h := TripleRestrictionRank.probability_mono β hβ hβ1
    (fun d : Draw J => T < dropCount d) (fun _ => True) (fun _ _ => trivial)
  rw [TripleRestrictionRank.probability_univ] at h
  unfold tail
  exact_mod_cast h

/-- The three singleton outcomes combine to one Bernoulli exponential factor. -/
lemma block_moment (β : ℚ) (t : ℝ) :
    (∑ b : BlockChoice, (blockMass β b : ℝ) * Real.exp (t * dropped b)) =
      1 - (β : ℝ) + (β : ℝ) * Real.exp t := by
  simp [Fintype.sum_option, blockMass, dropped, Fin.sum_univ_succ]
  <;> ring

/-- Exact factorization derived from `prior`, not an independence assumption. -/
theorem moment_identity (β : ℚ) (J : ℕ) (t : ℝ) :
    (∑ d : Draw J, (prior β d : ℝ) * Real.exp (t * dropCount d)) =
      (1 - (β : ℝ) + (β : ℝ) * Real.exp t) ^ J := by
  calc
    _ = ∑ d : Draw J, ∏ j : Fin J,
        ((blockMass β (d j) : ℝ) * Real.exp (t * dropped (d j))) := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [dropCount_cast, Finset.mul_sum, FiniteConcentration.exp_finite_sum,
        prior, FiniteSampling.trialMass, Rat.cast_prod, Finset.prod_mul_distrib]
    _ = ∏ _j : Fin J, ∑ b : BlockChoice,
        (blockMass β b : ℝ) * Real.exp (t * dropped b) := by
      rw [Fintype.prod_sum]
    _ = _ := by simp only [block_moment, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Poisson exponential envelope for the exact product moment. -/
theorem moment_bound (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J : ℕ) (t : ℝ) :
    (∑ d : Draw J, (prior β d : ℝ) * Real.exp (t * dropCount d)) ≤
      Real.exp ((J : ℝ) * (β : ℝ) * (Real.exp t - 1)) := by
  rw [moment_identity]
  have hp : (0 : ℝ) ≤ β := by exact_mod_cast hβ
  have hp1 : (β : ℝ) ≤ 1 := by exact_mod_cast hβ1
  have hn : 0 ≤ 1 - (β : ℝ) + (β : ℝ) * Real.exp t :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos t).le)
  have hb : 1 - (β : ℝ) + (β : ℝ) * Real.exp t ≤
      Real.exp ((β : ℝ) * (Real.exp t - 1)) := by
    have he := Real.add_one_le_exp ((β : ℝ) * (Real.exp t - 1))
    nlinarith only [he]
  calc
    _ ≤ (Real.exp ((β : ℝ) * (Real.exp t - 1))) ^ J :=
      pow_le_pow_left₀ hn hb J
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Strict integer tail bounded at the (weaker) real threshold T. t=0 is allowed. -/
theorem exponential_tail (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (J T : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    tail β J T ≤ Real.exp ((J : ℝ) * (β : ℝ) * (Real.exp t - 1) - t * T) := by
  have hs : tail β J T * Real.exp (t * T) ≤
      ∑ d : Draw J, (prior β d : ℝ) * Real.exp (t * dropCount d) := by
    rw [tail_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    have hd : (0 : ℝ) ≤ prior β d := by
      exact_mod_cast drawMass_nonneg β hβ hβ1 d
    split_ifs with he
    · have he' : (T : ℝ) ≤ dropCount d := by exact_mod_cast he.le
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he' ht)) hd
    · simpa using mul_nonneg hd (Real.exp_pos _).le
  have h := hs.trans (moment_bound β hβ hβ1 J t)
  apply (le_div_iff₀ (Real.exp_pos (t * T))).mpr at h
  simpa only [← Real.exp_sub] using h

/-- Optimized exponent, retaining the extra exp(-J beta) factor. -/
theorem optimized_tail (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (J T : ℕ) (hμ : 0 < (J : ℝ) * (β : ℝ))
    (hT : (J : ℝ) * (β : ℝ) ≤ T) :
    tail β J T ≤ Real.exp ((T : ℝ) - (J : ℝ) * (β : ℝ) -
      (T : ℝ) * Real.log ((T : ℝ) / ((J : ℝ) * (β : ℝ)))) := by
  have htpos : (0 : ℝ) < T := lt_of_lt_of_le hμ hT
  have hr : 0 < (T : ℝ) / ((J : ℝ) * (β : ℝ)) := div_pos htpos hμ
  have ht : 0 ≤ Real.log ((T : ℝ) / ((J : ℝ) * (β : ℝ))) :=
    Real.log_nonneg ((le_div_iff₀ hμ).mpr (by simpa using hT))
  have h := exponential_tail β hβ hβ1 J T
    (Real.log ((T : ℝ) / ((J : ℝ) * (β : ℝ)))) ht
  rw [Real.exp_log hr] at h
  have hid : (J : ℝ) * (β : ℝ) * ((T : ℝ) / ((J : ℝ) * (β : ℝ)) - 1) -
      Real.log ((T : ℝ) / ((J : ℝ) * (β : ℝ))) * T =
      (T : ℝ) - (J : ℝ) * (β : ℝ) -
        (T : ℝ) * Real.log ((T : ℝ) / ((J : ℝ) * (β : ℝ))) := by
    field_simp [(mul_ne_zero_iff.mp (ne_of_gt hμ)).1,
      (mul_ne_zero_iff.mp (ne_of_gt hμ)).2]
    <;> ring
  rwa [hid] at h

/-- Manuscript natural-cutoff form: Pr[D > T] <= (e J beta / T)^T. -/
theorem chernoff_tail (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (J T : ℕ) (hμ : 0 < (J : ℝ) * (β : ℝ))
    (hT : (J : ℝ) * (β : ℝ) ≤ T) :
    tail β J T ≤ (Real.exp 1 * ((J : ℝ) * (β : ℝ)) / T) ^ T := by
  have htpos : (0 : ℝ) < T := lt_of_lt_of_le hμ hT
  have hr : 0 < (T : ℝ) / ((J : ℝ) * (β : ℝ)) := div_pos htpos hμ
  have h := optimized_tail β hβ hβ1 J T hμ hT
  apply h.trans
  calc
    _ ≤ Real.exp ((T : ℝ) - (T : ℝ) *
        Real.log ((T : ℝ) / ((J : ℝ) * (β : ℝ)))) :=
      Real.exp_le_exp.mpr (by linarith only [hμ])
    _ = (Real.exp (1 - Real.log ((T : ℝ) / ((J : ℝ) * (β : ℝ))))) ^ T := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by
      congr 1
      rw [Real.exp_sub, Real.exp_log hr]
      field_simp [ne_of_gt hμ, ne_of_gt htpos]

lemma tail_zero_of_le (β : ℚ) (J T : ℕ) (hJT : J ≤ T) : tail β J T = 0 := by
  rw [tail_sum]
  apply Finset.sum_eq_zero
  intro d _
  exact if_neg (not_lt.mpr ((dropCount_le d).trans hJT))

lemma tail_empty (β : ℚ) (T : ℕ) : tail β 0 T = 0 :=
  tail_zero_of_le β 0 T (Nat.zero_le T)

lemma prior_zero_of_drop (d : Draw J) (hd : 0 < dropCount d) : prior 0 d = 0 := by
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hd
  have hj' : d j ≠ none := (Finset.mem_filter.mp hj).2
  unfold prior FiniteSampling.trialMass
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  cases h : d j with
  | none => exact False.elim (hj' h)
  | some k => simp [blockMass, h]

lemma tail_beta_zero (J T : ℕ) : tail 0 J T = 0 := by
  rw [tail_sum]
  apply Finset.sum_eq_zero
  intro d _
  split_ifs with hd
  · rw [prior_zero_of_drop d (lt_of_le_of_lt (Nat.zero_le T) hd)]
    simp
  · rfl

/-- Mean-zero case explicitly covers both J=0 and beta=0. -/
lemma tail_mean_zero (β : ℚ) (J T : ℕ) (hμ : (J : ℝ) * (β : ℝ) = 0) :
    tail β J T = 0 := by
  rcases mul_eq_zero.mp hμ with hJ | hβ
  · have hJ' : J = 0 := by exact_mod_cast hJ
    subst J
    exact tail_empty β T
  · have hβ' : β = 0 := by exact_mod_cast hβ
    subst β
    exact tail_beta_zero J T

/-- Also allows zero mean. At T=0 the displayed bound uses Lean's 0^0=1 convention. -/
theorem chernoff_tail_allow_zero (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (J T : ℕ) (hT : (J : ℝ) * (β : ℝ) ≤ T) :
    tail β J T ≤ (Real.exp 1 * ((J : ℝ) * (β : ℝ)) / T) ^ T := by
  have hμ : 0 ≤ (J : ℝ) * (β : ℝ) :=
    mul_nonneg (Nat.cast_nonneg J) (by exact_mod_cast hβ)
  rcases eq_or_lt_of_le hμ with hz | hp
  · rw [tail_mean_zero β J T hz.symm]
    exact pow_nonneg (div_nonneg
      (mul_nonneg (Real.exp_pos 1).le hμ) (Nat.cast_nonneg T)) T
  · exact chernoff_tail β hβ hβ1 J T hp hT

end
end PvNP.RealizableHardness.DropCountTail
