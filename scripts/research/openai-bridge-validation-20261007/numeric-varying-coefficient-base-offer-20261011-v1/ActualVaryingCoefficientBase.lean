import PvNP.RealizableHardness.ActualSelectedCompletionPosteriorBound

/-! Same-index completion and proximity bounds when the sampler coefficient
is fixed separately for each candidate index. No effective selector or
uniform-in-L runtime assertion. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVaryingCoefficientBase

open ActualSelectedCompletionPosteriorBound ActualNumericExplicitHeight
open ActualNumericSourceHeight ActualCmmsaAdmissibilitySelector
open ActualCmmsaParameterReconciliation ActualOccurrenceAllocation
open ActualTaggedConcreteStarLaw ActualCompletionEquationPullback
open ActualVaryingCompletionException SamplerParameters
open PosteriorReweighting PosteriorDensity GrassmannIncidence

set_option autoImplicit false
noncomputable section

/-- Each candidate uses its own coefficient, rank cap and actual thresholds. -/
def pointwiseCommonBase (base0 coefficient : Nat → Nat)
    (hA : ∀ j, 0 < coefficient j) (j : Nat) : Nat :=
  selectedCommonBase base0 (coefficient j) (hA j) j

theorem pointwiseCommonBase_bounds (base0 coefficient : Nat → Nat)
    (hA : ∀ j, 0 < coefficient j) (j : Nat) :
    base0 j ≤ pointwiseCommonBase base0 coefficient hA j ∧
    proximityThreshold (coefficient j) (numericRankThreshold j) (hA j) ≤
      pointwiseCommonBase base0 coefficient hA j ∧
    actualTailThreshold (coefficient j) (hA j) ≤
      pointwiseCommonBase base0 coefficient hA j ∧
    numericRankThreshold j ≤ pointwiseCommonBase base0 coefficient hA j ∧
    16 ≤ pointwiseCommonBase base0 coefficient hA j := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_max_left _ _
  · exact proximityThreshold_le_selectedCommonBase base0 (coefficient j) j (hA j)
  · exact actualTailThreshold_le_selectedCommonBase base0 (coefficient j) j (hA j)
  · exact numericRank_le_selectedCommonBase base0 (coefficient j) j (hA j)
  · exact sixteen_le_selectedCommonBase base0 (coefficient j) j (hA j)

/-- The selected lower bound directly supplies readiness and the actual
completion estimate at the same index and its own coefficient. -/
theorem pointwise_completion_bound (base0 coefficient : Nat → Nat)
    (hA : ∀ j, 0 < coefficient j) (m h : Nat)
    (hbase : pointwiseCommonBase base0 coefficient hA m ≤ h)
    {N rows : Nat} (I : Instance N rows) (copies : Nat) :
    SamplerProximity.Ready (coefficient m) (numericRankThreshold m) h ∧
    ∀ (U : TaggedGoodU I copies (blocks (coefficient m) h)) (a : Nat),
      a ≤ numericRankThreshold m →
      (mass (ambientMass : Advice (blocks (coefficient m) h) a → ℚ)
        (badPosterior (beta (coefficient m) h) (GoodAdvice.zeta h)
          (completionPulledBack I copies U)) : ℝ) ≤ DropTailParameters.decay 69 h := by
  have hb := pointwiseCommonBase_bounds base0 coefficient hA m
  have hP := hb.2.1.trans hbase
  have hT := hb.2.2.1.trans hbase
  have hR := hb.2.2.2.1.trans hbase
  have hh := hb.2.2.2.2.trans hbase
  refine ⟨proximityThreshold_spec (coefficient m) (numericRankThreshold m) h (hA m) hP, ?_⟩
  intro U a ha
  exact completion_badPosterior_mass_le_decay69 (coefficient m)
    (numericRankThreshold m) h a (hA m) hh hR hP hT ha I copies U

/-- Selector existence is applied to the actual pointwise floor. No witness
selected under a smaller or constant-coefficient floor is reused. -/
theorem selected_varying_completion_eventually (base0 coefficient : Nat → Nat)
    (hA : ∀ j, 0 < coefficient j) (cutoff : ℝ → Nat) (M : Nat)
    {N rows : Nat} (I : Instance N rows) (copies : Nat) :
    ∃ L0, ∀ L, L0 ≤ L → ∃ m,
      selector (numericSourceFloor (pointwiseCommonBase base0 coefficient hA) cutoff) L =
        (m : WithBot Nat) ∧ M ≤ m ∧
      SamplerProximity.Ready (coefficient m) (numericRankThreshold m) (hBlock L m) ∧
      ∀ (U : TaggedGoodU I copies (blocks (coefficient m) (hBlock L m))) (a : Nat),
        a ≤ numericRankThreshold m →
        (mass (ambientMass : Advice (blocks (coefficient m) (hBlock L m)) a → ℚ)
          (badPosterior (beta (coefficient m) (hBlock L m)) (GoodAdvice.zeta (hBlock L m))
            (completionPulledBack I copies U)) : ℝ) ≤
          DropTailParameters.decay 69 (hBlock L m) := by
  obtain ⟨L0, hselected⟩ := selected_explicit_numeric_parameters_eventually
    (pointwiseCommonBase base0 coefficient hA) cutoff 1 M (by decide)
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, hfacts⟩ := hselected L hL
  have hbound := pointwise_completion_bound base0 coefficient hA m (hBlock L m)
    hfacts.2.2.2.1 I copies
  exact ⟨m, hfacts.1, hfacts.2.1, hbound.1, hbound.2⟩

end
end PvNP.RealizableHardness.ActualVaryingCoefficientBase
