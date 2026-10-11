import PvNP.RealizableHardness.ActualVaryingCompletionExceptionApplication
import PvNP.RealizableHardness.ActualNumericExplicitHeight
import PvNP.RealizableHardness.ActualNumericRobustCutoffs
import PvNP.RealizableHardness.GoodAdvice

/-! Selected actual-sampler numerical specialization of the varying-completion
posterior theorem. The common selected base below is mathematically sufficient;
its proximity-threshold choice is non-effective. -/
namespace PvNP.RealizableHardness.ActualSelectedCompletionPosteriorBound

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualNumericExplicitHeight
open PvNP.RealizableHardness.ActualNumericSourceHeight
open PvNP.RealizableHardness.ActualNumericRobustCutoffs
open PvNP.RealizableHardness.ActualVaryingCompletionException
open PvNP.RealizableHardness.ActualVaryingCompletionException.Application
open PvNP.RealizableHardness.ActualCompletionEquationPullback
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.SamplerProximity
open PvNP.RealizableHardness.DropTailParameters
open PvNP.RealizableHardness.GoodAdvice
open PvNP.RealizableHardness.AdviceExceptions
open PvNP.RealizableHardness.PosteriorReweighting (mass)
open PvNP.RealizableHardness.PosteriorDensity (ambientMass)
open PvNP.RealizableHardness.ActualOccurrenceAllocation (Instance)
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw (TaggedGoodU)
open PvNP.RealizableHardness.GrassmannIncidence (Advice)

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A chosen actual proximity threshold for this sampler coefficient and rank cap. -/
def proximityThreshold (A R : Nat) (hA : 0 < A) : Nat :=
  Classical.choose (SamplerProximity.eventually_ready A R hA)

lemma proximityThreshold_spec (A R h : Nat) (hA : 0 < A)
    (hN : proximityThreshold A R hA <= h) : SamplerProximity.Ready A R h :=
  Classical.choose_spec (SamplerProximity.eventually_ready A R hA) h hN

/-- The actual tail threshold for the prescribed deletion sampler. -/
def actualTailThreshold (A : Nat) (hA : 0 < A) : Nat :=
  Classical.choose (SamplerParameters.eventual_actual_tail A hA)

lemma actualTailThreshold_spec (A h : Nat) (hA : 0 < A)
    (hN : actualTailThreshold A hA <= h) :
    DropCountTail.tail (SamplerParameters.beta A h) (SamplerParameters.blocks A h) (h ^ 4) <=
        DropTailParameters.decay 100 h /\
      DropCountTail.tail (SamplerParameters.beta A h) (SamplerParameters.blocks A h) (h ^ 4) /
        DropTailParameters.decay 30 h <= DropTailParameters.decay 70 h := by
  exact Classical.choose_spec (SamplerParameters.eventual_actual_tail A hA) h hN

/-- Pointwise selected base for the moving rank cap R_j. The threshold choice is
classical; this definition makes no effective-cutoff claim. -/
def selectedCommonBase (base0 : Nat -> Nat) (A : Nat) (hA : 0 < A)
    (j : Nat) : Nat :=
  max (base0 j)
    (max (proximityThreshold A (ActualNumericSourceHeight.numericRankThreshold j) hA)
      (max (actualTailThreshold A hA)
        (max (ActualNumericSourceHeight.numericRankThreshold j) 16)))

lemma proximityThreshold_le_selectedCommonBase
    (base0 : Nat -> Nat) (A j : Nat) (hA : 0 < A) :
    proximityThreshold A (ActualNumericSourceHeight.numericRankThreshold j) hA <=
      selectedCommonBase base0 A hA j := by
  dsimp [selectedCommonBase]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

lemma actualTailThreshold_le_selectedCommonBase
    (base0 : Nat -> Nat) (A j : Nat) (hA : 0 < A) :
    actualTailThreshold A hA <= selectedCommonBase base0 A hA j := by
  dsimp [selectedCommonBase]
  exact (Nat.le_max_left _ _).trans
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

lemma numericRank_le_selectedCommonBase
    (base0 : Nat -> Nat) (A j : Nat) (hA : 0 < A) :
    ActualNumericSourceHeight.numericRankThreshold j <= selectedCommonBase base0 A hA j := by
  dsimp [selectedCommonBase]
  exact (Nat.le_max_right _ _).trans
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)))

lemma sixteen_le_selectedCommonBase
    (base0 : Nat -> Nat) (A j : Nat) (hA : 0 < A) :
    16 <= selectedCommonBase base0 A hA j := by
  dsimp [selectedCommonBase]
  exact (Nat.le_max_right _ _).trans
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))

/-- The actual double-exponential block count pays the h^4 deletion loss. -/
lemma blocks_ge_four_h4 {A h : Nat} (hA : 1 <= A) (hh : 16 <= h) :
    4 * h ^ 4 <= SamplerParameters.blocks A h := by
  let n := h ^ 2
  have hn4 : 4 <= n := by dsimp [n]; nlinarith
  have hn_sq : n ^ 2 <= 2 ^ n := by
    induction n, hn4 using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [pow_succ (2 : Nat) n]
        nlinarith
  have hn_plus : n + 2 <= 2 ^ n := by
    induction n, hn4 using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [pow_succ]
        omega
  have hAn : n <= A * n := by
    simpa using Nat.mul_le_mul_right n hA
  have hq : n + 2 <= 2 ^ (A * n) :=
    hn_plus.trans (Nat.pow_le_pow_right (by norm_num) hAn)
  calc
    4 * h ^ 4 = 4 * n ^ 2 := by dsimp [n]; ring
    _ <= 4 * 2 ^ n := Nat.mul_le_mul_left 4 hn_sq
    _ = 2 ^ (n + 2) := by rw [pow_add]; norm_num; ring
    _ <= 2 ^ (2 ^ (A * n)) := Nat.pow_le_pow_right (by norm_num) hq
    _ = SamplerParameters.blocks A h := by simp [SamplerParameters.blocks, n]

/-- Actual selected completion posterior bound once the two actual thresholds
are met. No tail or TV event-mass premise is supplied. -/
theorem completion_badPosterior_mass_le_decay69
    (A R h a : Nat) (hA : 1 <= A) (hh : 16 <= h)
    (hR : R <= h) (hP : proximityThreshold A R (by omega : 0 < A) <= h)
    (hT : actualTailThreshold A (by omega : 0 < A) <= h)
    (ha : a <= R)
    {N rows : Nat} (I : Instance N rows) (copies : Nat)
    (U : TaggedGoodU I copies (SamplerParameters.blocks A h)) :
    (mass (ambientMass : Advice (SamplerParameters.blocks A h) a -> ℚ)
      (badPosterior (SamplerParameters.beta A h) (GoodAdvice.zeta h)
        (completionPulledBack I copies U)) : ℝ) <= DropTailParameters.decay 69 h := by
  have hApos : 0 < A := by omega
  have hready := proximityThreshold_spec A R h hApos hP
  have htail := actualTailThreshold_spec A h hApos hT
  have hdim := SamplerProximity.ready_dimensions hready
  have haJ : a <= SamplerParameters.blocks A h := by omega
  have hβ := SamplerParameters.beta_nonneg A h
  have hβ1 := SamplerParameters.beta_le_one A h
  have hζ := GoodAdvice.zeta_pos h
  let J := SamplerParameters.blocks A h
  let E := 2 * J - 2 * h ^ 4 - a - 1
  have hJ := blocks_ge_four_h4 hA hh
  have hsmall : 100 * h ^ 2 + a + 1 + 2 * h ^ 4 <= 2 * J := by
    have hsq : 256 * h ^ 2 <= h ^ 4 := by
      have hh2 : 256 <= h ^ 2 := by nlinarith
      have hp := Nat.mul_le_mul_right (h ^ 2) hh2
      nlinarith [hp]
    have hsize : 100 * h ^ 2 + a + 1 + 2 * h ^ 4 <= 8 * h ^ 4 := by
      have haH : a <= h := ha.trans hR
      nlinarith [hsq, haH]
    have hmul := Nat.mul_le_mul_left 2 hJ
    nlinarith
  have hE : 100 * h ^ 2 <= E := by dsimp [E, J]; omega
  have hslack : J + a + 1 <= 3 * J - 2 * h ^ 4 := by dsimp [J]; omega
  have hmain := actual_completion_badPosterior_ambient_mass_le I copies U
    (SamplerParameters.beta A h) hβ hβ1 haJ (h ^ 4) hslack
    (GoodAdvice.zeta h) hζ
  have hmainR :
      (mass (ambientMass : Advice J a -> ℚ)
        (badPosterior (SamplerParameters.beta A h) (GoodAdvice.zeta h)
          (completionPulledBack I copies U)) : ℝ) <=
      (((AdviceExceptions.priorTail (SamplerParameters.beta A h) J (h ^ 4) +
        1 / (2 : ℚ) ^ E) / GoodAdvice.zeta h +
          AdviceExceptions.adviceTV (SamplerParameters.beta A h) J a : ℚ) : ℝ) := by
    exact_mod_cast hmain
  push_cast at hmainR
  rw [GoodAdvice.zeta_cast, add_div] at hmainR
  have htailR :
      (AdviceExceptions.priorTail (SamplerParameters.beta A h) J (h ^ 4) : ℝ) /
        DropTailParameters.decay 30 h <= DropTailParameters.decay 70 h := by
    rw [AdviceExceptions.priorTail_cast]
    exact htail.2
  have htv : (AdviceExceptions.adviceTV (SamplerParameters.beta A h) J a : ℝ) <=
      DropTailParameters.decay 100 h := by
    have ht := CoveringSpan.actual_adviceTV_le_manuscript
      (SamplerParameters.beta A h) hβ hβ1 haJ
    change (AdviceExceptions.tv (PosteriorDensity.ambientMass) (adviceMarginal (SamplerParameters.beta A h)) : ℝ) <= _
    exact ht.trans (SamplerProximity.ready_advice hready ha)
  have hpowNat : 2 ^ (100 * h ^ 2) <= 2 ^ E :=
    Nat.pow_le_pow_right (by norm_num) hE
  have hpowReal : (2 : ℝ) ^ (100 * h ^ 2) <= (2 : ℝ) ^ E := by
    exact_mod_cast hpowNat
  have hdyadCast : ((1 / (2 : ℚ) ^ E : ℚ) : ℝ) <=
      1 / (2 : ℝ) ^ (100 * h ^ 2) := by
    have hcast : ((1 / (2 : ℚ) ^ E : ℚ) : ℝ) = 1 / (2 : ℝ) ^ E := by norm_num
    rw [hcast]
    exact one_div_le_one_div_of_le (by positivity) hpowReal
  have hratio :
      (1 / (2 : ℝ) ^ (100 * h ^ 2)) / DropTailParameters.decay 30 h =
        DropTailParameters.decay 70 h := by
    rw [← DropTailParameters.decay_eq_reciprocal 100 h,
      DropTailParameters.decay_add 70 30 h]
    exact mul_div_cancel_right₀ _ (ne_of_gt (DropTailParameters.decay_pos 30 h))
  have hdyad :
      ((1 / (2 : ℚ) ^ E : ℚ) : ℝ) / (GoodAdvice.zeta h : ℝ) <=
        DropTailParameters.decay 70 h := by
    rw [GoodAdvice.zeta_cast]
    calc
      _ <= (1 / (2 : ℝ) ^ (100 * h ^ 2)) / DropTailParameters.decay 30 h :=
        div_le_div_of_nonneg_right hdyadCast (DropTailParameters.decay_pos 30 h).le
      _ = DropTailParameters.decay 70 h := hratio
  have hD100 : DropTailParameters.decay 100 h <= DropTailParameters.decay 70 h :=
    SamplerProximity.decay_antitone (by norm_num)
  have hD70 : 3 * DropTailParameters.decay 70 h <= DropTailParameters.decay 69 h := by
    have hsq : 2 <= h ^ 2 := by nlinarith
    have hpNat : 4 <= 2 ^ (h ^ 2) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ <= 2 ^ (h ^ 2) := Nat.pow_le_pow_right (by norm_num) hsq
    have hpReal4 : (4 : ℝ) <= (2 : ℝ) ^ (h ^ 2) := by exact_mod_cast hpNat
    have hpReal : (3 : ℝ) <= (2 : ℝ) ^ (h ^ 2) := by linarith
    have hD1 : 3 * DropTailParameters.decay 1 h <= 1 := by
      rw [DropTailParameters.decay_eq_reciprocal]
      simp only [Nat.one_mul]
      calc
        3 * (1 / (2 : ℝ) ^ (h ^ 2)) = 3 / (2 : ℝ) ^ (h ^ 2) := by ring
        _ <= 1 := (div_le_one₀ (by positivity)).2 hpReal
    have hdec : DropTailParameters.decay 70 h =
        DropTailParameters.decay 69 h * DropTailParameters.decay 1 h := by
      simpa using DropTailParameters.decay_add 69 1 h
    rw [hdec]
    calc
      3 * (DropTailParameters.decay 69 h * DropTailParameters.decay 1 h) =
          DropTailParameters.decay 69 h * (3 * DropTailParameters.decay 1 h) := by ring
      _ <= DropTailParameters.decay 69 h := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hD1 (DropTailParameters.decay_pos 69 h).le)
  calc
    _ <= _ := hmainR
    _ <= DropTailParameters.decay 70 h + DropTailParameters.decay 70 h +
        DropTailParameters.decay 100 h := by
      linarith [htailR, hdyad, htv]
    _ <= DropTailParameters.decay 69 h := by
      calc
        _ <= 3 * DropTailParameters.decay 70 h := by nlinarith
        _ <= _ := hD70

/-- Same-selector numerical theorem. The pointwise base includes the actual
proximity threshold for the moving rank cap and the actual sampler tail threshold. -/
theorem selected_completion_badPosterior_mass_eventually
    (base0 : Nat -> Nat) (cutoff : ℝ -> Nat) (A : Nat) (hA : 1 <= A)
    {N rows : Nat} (I : Instance N rows) (copies : Nat) :
    ∃ L0, ∀ L, L0 <= L -> ∃ m,
      ActualCmmsaAdmissibilitySelector.selector
        (ActualNumericExplicitHeight.numericSourceFloor
          (selectedCommonBase base0 A (by omega)) cutoff) L = (m : WithBot Nat) ∧
      ∀ (U : TaggedGoodU I copies
          (SamplerParameters.blocks A (ActualCmmsaParameterReconciliation.hBlock L m)))
        (a : Nat), a <= ActualNumericSourceHeight.numericRankThreshold m ->
        (mass (ambientMass : Advice
          (SamplerParameters.blocks A (ActualCmmsaParameterReconciliation.hBlock L m)) a -> ℚ)
          (badPosterior (SamplerParameters.beta A (ActualCmmsaParameterReconciliation.hBlock L m))
            (GoodAdvice.zeta (ActualCmmsaParameterReconciliation.hBlock L m))
            (completionPulledBack I copies U)) : ℝ) <=
          DropTailParameters.decay 69 (ActualCmmsaParameterReconciliation.hBlock L m) := by
  have hApos : 0 < A := by omega
  obtain ⟨L0, hSelected⟩ := ActualNumericExplicitHeight.selected_explicit_numeric_parameters_eventually
    (selectedCommonBase base0 A hApos) cutoff A 256 hA
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, hfacts⟩ := hSelected L hL
  rcases hfacts with ⟨hsel, _⟩
  refine ⟨m, hsel, ?_⟩
  intro U a ha
  have hselSource : ActualCmmsaAdmissibilitySelector.selector
      (fun j => max
        (ActualCmmsaParameterReconciliation.analyticSourceHeightFloor
          (ActualNumericSourceHeight.numericSourceBase
            (ActualNumericExplicitHeight.numericBase (selectedCommonBase base0 A hApos))) cutoff j)
        (j + 2)) L = (m : WithBot Nat) := by
    simpa [ActualNumericExplicitHeight.numericSourceFloor,
      ActualNumericExplicitHeight.numericSourceBase_eq] using hsel
  rcases ActualNumericSourceHeight.selected_numeric_height
      (ActualNumericExplicitHeight.numericBase (selectedCommonBase base0 A hApos)) cutoff hselSource with
    ⟨_, hRank, hnumBase, _, _⟩
  have hbase : selectedCommonBase base0 A hApos m <=
      ActualCmmsaParameterReconciliation.hBlock L m :=
    (Nat.le_max_left _ _).trans hnumBase
  have hP := (proximityThreshold_le_selectedCommonBase base0 A m hApos).trans hbase
  have hT := (actualTailThreshold_le_selectedCommonBase base0 A m hApos).trans hbase
  have hrob := ActualNumericRobustCutoffs.selected_robust_dimension_guards
    (selectedCommonBase base0 A hApos) cutoff hA hsel
  have hh : 16 <= ActualCmmsaParameterReconciliation.hBlock L m := hrob.2.2.1
  exact completion_badPosterior_mass_le_decay69 A
    (ActualNumericSourceHeight.numericRankThreshold m)
    (ActualCmmsaParameterReconciliation.hBlock L m) a hA hh hRank hP hT ha I copies U

end
end PvNP.RealizableHardness.ActualSelectedCompletionPosteriorBound
