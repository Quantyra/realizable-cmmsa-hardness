import PvNP.RealizableHardness.CoveringSpan

/-! UNCOMPILED checks. No axiom output or example acceptance has run yet. -/
namespace PvNP.RealizableHardness.CoveringSpanChecks
open scoped BigOperators
open CoveringSpan GrassmannCounting TripleRestrictionRank GrassmannIncidence

#print axioms push_tv_le
#print axioms mixture_tv_le
#print axioms sum_over_frames
#print axioms spanKernel_sum
#print axioms push_uniformArray
#print axioms failureFraction_eq
#print axioms failureFraction_le
#print axioms push_rawArrayLaw
#print axioms subspaceArrayPush_eq
#print axioms subspaceArrayPush_tv_le
#print axioms arrayCoordinates
#print axioms arrayCoordinates_mem_iff
#print axioms retained_array_card
#print axioms rawArrayLaw_coordinates
#print axioms blockArrayMass_mixture
#print axioms rawArrayLaw_mixture_coordinates
#print axioms uniformArray_coordinates
#print axioms retained_eq_top_of_no_drop
#print axioms deletion_probability_le
#print axioms retained_failure_le
#print axioms retained_correction_le
#print axioms averaged_retained_correction_le
#print axioms averaged_subspaceLaw_eq_adviceMarginal
#print axioms push_uniform_coordinates
#print axioms push_deleted_coordinates
#print axioms actual_advice_tv_le
#print axioms size_over_two_pow_le_sqrt
#print axioms rank_correction_absorption
#print axioms actual_advice_tv_le_manuscript
#print axioms rationalTV_cast
#print axioms actual_adviceTV_le_manuscript

noncomputable section
attribute [local instance] Classical.propDecidable

example (x : Fin 2 → CoveringTV.Cube (Fin 1 → ZMod 2)) :
    (arrayCoordinates 2 1).symm (arrayCoordinates 2 1 x) = x :=
  (arrayCoordinates 2 1).symm_apply_apply x

example (v : Fin 2 → Vector 3) :
    arrayCoordinates 3 2 ((arrayCoordinates 3 2).symm v) = v :=
  (arrayCoordinates 3 2).apply_symm_apply v

example (d : Draw J) (hd : TripleRestrictionDimension.dropCount d = 0) :
    retained d = ⊤ := retained_eq_top_of_no_drop d hd

example (d : Draw 3) : failureFraction (retained d) 1 ≤ 1 / 8 := by
  convert retained_failure_le (a := 1) d (by omega) using 1 <;> norm_num

example (J a : ℕ) (ha : a ≤ J) :
    CoveringTV.realTV (fun Q : Advice J a => (PosteriorDensity.ambientMass Q : ℝ))
      (fun Q => (adviceMarginal 0 Q : ℝ)) ≤ 0 := by
  simpa using actual_advice_tv_le 0 (by norm_num) (by norm_num) ha

example (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    CoveringTV.realTV (fun Q : Advice 0 0 => (PosteriorDensity.ambientMass Q : ℝ))
      (fun Q => (adviceMarginal β Q : ℝ)) ≤ 0 := by
  simpa using actual_advice_tv_le β hβ hβ1 (J := 0) (a := 0) le_rfl

example (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    probability β (fun d : Draw 1 => 0 < TripleRestrictionDimension.dropCount d) ≤ β := by
  simpa using deletion_probability_le β hβ hβ1 1

example (β : ℚ) (Q : Advice 1 1) :
    (∑ d : Draw 1, (prior β d : ℝ) * subspaceLaw (retained d) Q) =
      (adviceMarginal β Q : ℝ) := averaged_subspaceLaw_eq_adviceMarginal β Q

example : (0 : ℝ) / (2 : ℝ)^0 ≤ Real.sqrt 0 := by
  simpa using size_over_two_pow_le_sqrt 0

example (J a : ℕ) (ha : a ≤ J) :
    CoveringTV.realTV (fun Q : Advice J a => (PosteriorDensity.ambientMass Q : ℝ))
      (fun Q => (adviceMarginal 0 Q : ℝ)) ≤ 0 := by
  simpa using actual_advice_tv_le_manuscript 0 (by norm_num) (by norm_num) ha

end
end PvNP.RealizableHardness.CoveringSpanChecks
