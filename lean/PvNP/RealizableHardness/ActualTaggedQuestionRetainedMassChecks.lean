import PvNP.RealizableHardness.ActualTaggedQuestionRetainedMass

namespace PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualQuestionMassBridge
noncomputable section

#check actualTaggedGoodQuestions
#check actualTaggedBadQuestions
#check actualTaggedGoodMass
#check actualTaggedBadMass
#check actual_tagged_bad_ordered_question_uniform_mass_le
#check actual_tagged_bad_mass_padding_le
#check actual_tagged_bad_mass_le_quarter
#check actual_tagged_good_bad_card_add_eq_total
#check actual_tagged_total_question_count_pos
#check actual_tagged_good_mass_eq_one_sub_bad_mass
#check actual_tagged_good_mass_ge_three_quarters
#check actual_tagged_good_card_pos
#check actual_tagged_conditioning_factor_le_four_thirds
#check actual_tagged_conditioning_factor_lt_two

#print axioms actualTaggedGoodQuestions
#print axioms actualTaggedBadQuestions
#print axioms actualTaggedGoodMass
#print axioms actualTaggedBadMass
#print axioms actual_tagged_bad_ordered_question_uniform_mass_le
#print axioms actual_tagged_bad_mass_padding_le
#print axioms actual_tagged_bad_mass_le_quarter
#print axioms actual_tagged_good_bad_card_add_eq_total
#print axioms actual_tagged_total_question_count_pos
#print axioms actual_tagged_good_mass_eq_one_sub_bad_mass
#print axioms actual_tagged_good_mass_ge_three_quarters
#print axioms actual_tagged_good_card_pos
#print axioms actual_tagged_conditioning_factor_le_four_thirds
#print axioms actual_tagged_conditioning_factor_lt_two

def smallActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 0

example : actualPaddingCopies 0 4 = 1 := by
  norm_num [actualPaddingCopies]

example : actualPaddingCopies 1 4 = 1 := by
  norm_num [actualPaddingCopies]

example : actualPaddingCopies 2 4 = 1257 := by
  norm_num [actualPaddingCopies]

example : actualTaggedBadMass smallActual (actualPaddingCopies 0 4) 0 ≤
    (1 : ℚ) / 4 := by
  apply actual_tagged_bad_mass_le_quarter smallActual 0 4
  norm_num
  norm_num

example : actualTaggedBadMass smallActual (actualPaddingCopies 1 4) 1 ≤
    (1 : ℚ) / 4 := by
  apply actual_tagged_bad_mass_le_quarter smallActual 1 4
  norm_num
  norm_num

example : 0 <
    (actualTaggedGoodQuestions smallActual (actualPaddingCopies 2 4) 2).card := by
  apply actual_tagged_good_card_pos smallActual 2 4
  norm_num
  norm_num

end
end PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
