import PvNP.RealizableHardness.ActualTaggedQuestionRetainedMass
import PvNP.RealizableHardness.ActualLateTauYesComposition
import PvNP.RealizableHardness.Finite3LinOptimum

/-! The manuscript's late-τ choice of disjoint source copies, connected to
the actual ordered copied-row question law. The resampled-block YES marginals
remain separate hypotheses in `ActualLateTauYesComposition`. -/

namespace PvNP.RealizableHardness.ActualLateTauPadding

open ActualQuestionMassBridge
open ActualOccurrenceAllocation
open Finite3LinSource

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Once `J` is fixed, any later positive rational `τ` admits a fixed copy
count whose actual illegitimate ordered-question mass is at most both budgets
in manuscript §7. -/
theorem exists_late_tau_padding {N m J : Nat}
    (I : Instance N m) (hm : 0 < m) (τ : ℚ) (hτ : 0 < τ) :
    ∃ T : Nat, 4 ≤ T ∧
      let copies := actualPaddingCopies J T
      actualTaggedBadMass I copies J ≤ τ / 100 ∧
      actualTaggedBadMass I copies J ≤ (1 : ℚ) / 4 ∧
      actualTaggedGoodMass I copies J =
        1 - actualTaggedBadMass I copies J := by
  obtain ⟨T, hT⟩ := exists_nat_gt (max (4 : ℚ) (100 / τ))
  have hfour : 4 ≤ T := by
    have : (4 : ℚ) < T := lt_of_le_of_lt (le_max_left _ _) hT
    exact_mod_cast this.le
  have hquot : 100 / τ < (T : ℚ) :=
    lt_of_le_of_lt (le_max_right _ _) hT
  have hTpos : 0 < T := by omega
  have hTq : (0 : ℚ) < T := by exact_mod_cast hTpos
  have hbudget : (1 : ℚ) / T ≤ τ / 100 := by
    apply (div_le_div_iff₀ hTq (by norm_num : (0 : ℚ) < 100)).2
    have : (100 : ℚ) ≤ (T : ℚ) * τ := by
      have := (div_lt_iff₀ hτ).mp hquot
      nlinarith
    nlinarith
  refine ⟨T, hfour, ?_, ?_, ?_⟩
  · exact (actual_tagged_bad_mass_padding_le I J T hTpos hm).trans hbudget
  · exact actual_tagged_bad_mass_le_quarter I J T hfour hm
  · exact actual_tagged_good_mass_eq_one_sub_bad_mass I
      (actualPaddingCopies J T) J (actualPaddingCopies_pos J T) hm

end
end PvNP.RealizableHardness.ActualLateTauPadding
