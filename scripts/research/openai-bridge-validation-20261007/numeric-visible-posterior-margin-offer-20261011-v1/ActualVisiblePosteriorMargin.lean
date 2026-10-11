import PvNP.RealizableHardness.ActualSelectedCompletionPosteriorBound
import PvNP.RealizableHardness.ActualNumericRobustReal
import PvNP.RealizableHardness.ZoomOutPosterior

/-! Scalar margin for the actual visible-table posterior comparison.
The same selected height and one fixed rational threshold are used throughout.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVisiblePosteriorMargin
open PvNP.RealizableHardness
open ActualSelectedCompletionPosteriorBound ActualNumericRobustCutoffs
open ActualNumericExplicitHeight ActualNumericSourceHeight ActualNumericRobustReal
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open SamplerParameters ZoomOutPosterior

set_option autoImplicit false
noncomputable section

/-- The actual retained-window exponent and interval slack follow from the
block count; the rank cap is the same cap as in the original decoder. -/
theorem actual_leaf_exponent_and_window_slack {A h r : Nat}
    (hA : 1 ≤ A) (hh : 16 ≤ h) (hr : r ≤ h) :
    10 * h ^ 2 ≤ 2 * blocks A h - 2 * h ^ 4 - 2 * h - r - 1 ∧
    blocks A h + 2 * h + 1 ≤ 3 * blocks A h - 2 * h ^ 4 - r := by
  have hJ := blocks_ge_four_h4 hA hh
  have hsq : 256 * h ^ 2 ≤ h ^ 4 := by
    have hh2 : 256 ≤ h ^ 2 := by nlinarith
    have hp := Nat.mul_le_mul_right (h ^ 2) hh2
    nlinarith [hp]
  have hlarge : 10 * h ^ 2 + 2 * h + r + 1 + 2 * h ^ 4 ≤
      2 * blocks A h := by
    nlinarith [hJ, hsq]
  constructor <;> omega

/-- The two actual leaf losses and four posterior exclusion charges fit
strictly inside half of the fixed threshold C>e/5. -/
theorem actual_visible_posterior_margin {A h r : Nat}
    (hA : 1 ≤ A) (hh : 16 ≤ h) (hr : r ≤ h)
    (e : ℝ) (C : ℚ)
    (he : 1 / (2 : ℝ) ^ (2 * h) ≤ e) (hC : e / 5 < (C : ℝ)) :
    qdecay 10 h + 2 / (2 : ℚ) ^
        (2 * blocks A h - 2 * h ^ 4 - 2 * h - r - 1) +
      4 * GoodAdvice.zeta h ≤ C / 2 := by
  let E := 2 * blocks A h - 2 * h ^ 4 - 2 * h - r - 1
  have hexp : 10 * h ^ 2 ≤ E := (actual_leaf_exponent_and_window_slack hA hh hr).1
  have hpow : (2 : ℚ) ^ (10 * h ^ 2) ≤ (2 : ℚ) ^ E :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hd : qdecay 10 h = 1 / (2 : ℚ) ^ (10 * h ^ 2) := by
    simp [qdecay, one_div_pow]
  have hleaf : 1 / (2 : ℚ) ^ E ≤ qdecay 10 h := by
    rw [hd]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hz : GoodAdvice.zeta h ≤ qdecay 10 h := by
    have hp : (2 : ℚ) ^ (10 * h ^ 2) ≤ (2 : ℚ) ^ (30 * h ^ 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simpa [GoodAdvice.zeta, qdecay, one_div_pow] using
      (one_div_le_one_div_of_le (show (0 : ℚ) < (2 : ℚ) ^ (10 * h ^ 2) by positivity) hp)
  have hgap : 2 * h + 7 ≤ 10 * h ^ 2 := by nlinarith
  have hpowGap : (2 : ℚ) ^ (2 * h + 7) ≤ (2 : ℚ) ^ (10 * h ^ 2) :=
    pow_le_pow_right₀ (by norm_num) hgap
  rw [pow_add] at hpowGap
  norm_num at hpowGap
  have h70 : 70 * (2 : ℚ) ^ (2 * h) ≤ (2 : ℚ) ^ (10 * h ^ 2) := by
    have hpos : 0 ≤ (2 : ℚ) ^ (2 * h) := by positivity
    nlinarith
  have hsmall : 7 * qdecay 10 h ≤ (1 / (2 : ℚ) ^ (2 * h)) / 10 := by
    rw [hd]
    calc
      7 * (1 / (2 : ℚ) ^ (10 * h ^ 2)) = 7 / (2 : ℚ) ^ (10 * h ^ 2) := by ring
      _ ≤ (1 / (2 : ℚ) ^ (2 * h)) / 10 := by
        rw [div_div]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [h70]
  have hCrat : (1 / (2 : ℚ) ^ (2 * h)) / 10 < C / 2 := by
    have hReal : (1 / (2 : ℝ) ^ (2 * h)) / 10 < (C : ℝ) / 2 := by
      linarith
    exact_mod_cast hReal
  have hcharge : qdecay 10 h + 2 / (2 : ℚ) ^ E + 4 * GoodAdvice.zeta h ≤
      7 * qdecay 10 h := by
    have hleaf2 : 2 / (2 : ℚ) ^ E ≤ 2 * qdecay 10 h := by
      have ht := mul_le_mul_of_nonneg_left hleaf (show (0 : ℚ) ≤ 2 by norm_num)
      simpa only [div_eq_mul_inv, one_mul] using ht
    linarith
  exact hcharge.trans (hsmall.trans hCrat.le)

/-- Selected specialization uses the existing robust floor and the original
refresh threshold; it does not choose a threshold after the draw. -/
theorem selected_visible_posterior_margin
    {L m A : Nat} (base : Nat → Nat) (cutoff : ℝ → Nat)
    (hA : 1 ≤ A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (C : ℚ) (hC : refreshThreshold m (hBlock L m) / 5 < (C : ℝ)) :
    qdecay 10 (hBlock L m) + 2 / (2 : ℚ) ^
        (2 * blocks A (hBlock L m) - 2 * (hBlock L m) ^ 4 -
          2 * hBlock L m - numericRankThreshold m - 1) +
      4 * GoodAdvice.zeta (hBlock L m) ≤ C / 2 ∧
    blocks A (hBlock L m) + 2 * hBlock L m + 1 ≤
      3 * blocks A (hBlock L m) - 2 * (hBlock L m) ^ 4 - numericRankThreshold m := by
  have hguards := selected_robust_dimension_guards base cutoff hA hsel
  rcases hguards with ⟨_, h8r, hh, _, _, _, _⟩
  have hr : numericRankThreshold m ≤ hBlock L m := by omega
  have hheightFacts := selected_numeric_height (numericBase base) cutoff
    (by simpa only [numericSourceBase_eq, numericSourceFloor] using hsel)
  rcases hheightFacts with
    ⟨hm, _, hheight, _, _⟩
  have hnum : numericHnum m ≤ hBlock L m :=
    (Nat.le_max_right (base m) (numericHnum m)).trans hheight
  have he := (refresh_threshold_bounds hm hnum).1
  exact ⟨actual_visible_posterior_margin hA hh hr _ C he hC,
    (actual_leaf_exponent_and_window_slack hA hh hr).2⟩

end
end PvNP.RealizableHardness.ActualVisiblePosteriorMargin
