import PvNP.RealizableHardness.ActualTaggedQuestionRetainedMass

namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open ActualOccurrenceAllocation
open Finite3LinSource
open scoped BigOperators
set_option autoImplicit false
noncomputable section

local instance conditioningActualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance conditioningActualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

local instance conditioningActualTaggedGoodDecidablePred {N m K J : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    DecidablePred (fun u : Fin J → Fin K × I.RowId =>
      GoodOrderedQuestion ((Finite3LinSource.ofActual I).taggedCopy K).support u) :=
  fun _ => Classical.propDecidable _

def actualTaggedUniformMean {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat)
    (f : (Fin J → Fin K × I.RowId) → ℝ) : ℝ :=
  (∑ u, f u) / (Fintype.card (Fin J → Fin K × I.RowId) : ℝ)

def actualTaggedGoodMean {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat)
    (f : (Fin J → Fin K × I.RowId) → ℝ) : ℝ :=
  (∑ u ∈ actualTaggedGoodQuestions I K J, f u) /
    ((actualTaggedGoodQuestions I K J).card : ℝ)

theorem actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m)
    (f : (Fin J → Fin (actualPaddingCopies J T) × I.RowId) → ℝ) :
    actualTaggedGoodMean I (actualPaddingCopies J T) J f =
      actualTaggedUniformMean I (actualPaddingCopies J T) J
        (fun u => if u ∈ actualTaggedGoodQuestions I (actualPaddingCopies J T) J
          then f u else 0) /
        (actualTaggedGoodMass I (actualPaddingCopies J T) J : ℝ) := by
  let U := Fin J → Fin (actualPaddingCopies J T) × I.RowId
  let G : Finset U := actualTaggedGoodQuestions I (actualPaddingCopies J T) J
  have htotal := actual_tagged_total_question_count_pos I
    (actualPaddingCopies J T) J (actualPaddingCopies_pos J T) hm
  have htotalQ : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast htotal
  have hgood := actual_tagged_good_card_pos I J T hT hm
  have hgoodQ : (0 : ℝ) < G.card := by
    exact_mod_cast hgood
  have hsum : (∑ u : U, (if u ∈ G then f u else 0)) = ∑ u ∈ G, f u := by
    rw [← Finset.sum_filter]
    simp [G]
  have hmass : (actualTaggedGoodMass I (actualPaddingCopies J T) J : ℝ) =
      (G.card : ℝ) / (Fintype.card U : ℝ) := by
    simp [actualTaggedGoodMass, G, U]
  unfold actualTaggedGoodMean actualTaggedUniformMean
  change (∑ u ∈ G, f u) / (G.card : ℝ) =
    (∑ u : U, (if u ∈ G then f u else 0)) /
      (Fintype.card U : ℝ) /
        (actualTaggedGoodMass I (actualPaddingCopies J T) J : ℝ)
  rw [hsum, hmass]
  let S : ℝ := ∑ u ∈ G, f u
  change S / (G.card : ℝ) =
    S / (Fintype.card U : ℝ) /
      ((G.card : ℝ) / (Fintype.card U : ℝ))
  field_simp [ne_of_gt hgoodQ, ne_of_gt htotalQ]

theorem actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m)
    (f : (Fin J → Fin (actualPaddingCopies J T) × I.RowId) → ℝ)
    (hf : ∀ u, 0 ≤ f u) :
    actualTaggedGoodMean I (actualPaddingCopies J T) J f ≤
      (4 : ℝ) / 3 * actualTaggedUniformMean I (actualPaddingCopies J T) J f := by
  have hidentity := actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass
    I J T hT hm f
  have hfactor := actual_tagged_conditioning_factor_le_four_thirds I J T hT hm
  have hfactorR : (1 : ℝ) /
      (actualTaggedGoodMass I (actualPaddingCopies J T) J : ℝ) ≤
      (4 : ℝ) / 3 := by
    have hr : (((1 : ℚ) / actualTaggedGoodMass I
        (actualPaddingCopies J T) J : ℚ) : ℝ) ≤
        (((4 : ℚ) / 3 : ℚ) : ℝ) := Rat.cast_le.mpr hfactor
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hr
  have hmasspos : (0 : ℝ) <
      (actualTaggedGoodMass I (actualPaddingCopies J T) J : ℝ) := by
    have h := actual_tagged_good_mass_ge_three_quarters I J T hT hm
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 3 / 4) h)
  have hsum_nonneg : 0 ≤ ∑ u, f u := by
    exact Finset.sum_nonneg (fun u hu => hf u)
  have huniform_nonneg : 0 ≤ actualTaggedUniformMean I
      (actualPaddingCopies J T) J f := by
    unfold actualTaggedUniformMean
    have htotalR : (0 : ℝ) < Fintype.card
        (Fin J → Fin (actualPaddingCopies J T) × I.RowId) := by
      have htotal := actual_tagged_total_question_count_pos I
        (actualPaddingCopies J T) J (actualPaddingCopies_pos J T) hm
      exact_mod_cast htotal
    exact div_nonneg hsum_nonneg (le_of_lt htotalR)
  rw [hidentity]
  have hgate : 0 ≤ actualTaggedUniformMean I (actualPaddingCopies J T) J
      (fun u => if u ∈ actualTaggedGoodQuestions I (actualPaddingCopies J T) J
        then f u else 0) := by
    unfold actualTaggedUniformMean
    apply div_nonneg
    · exact Finset.sum_nonneg (fun u hu => by split_ifs <;> linarith [hf u])
    · have htotalR : (0 : ℝ) < Fintype.card
          (Fin J → Fin (actualPaddingCopies J T) × I.RowId) := by
        have htotal := actual_tagged_total_question_count_pos I
          (actualPaddingCopies J T) J (actualPaddingCopies_pos J T) hm
        exact_mod_cast htotal
      exact htotalR.le
  have hmul := mul_le_mul_of_nonneg_right hfactorR hgate
  calc
    actualTaggedUniformMean I (actualPaddingCopies J T) J
        (fun u => if u ∈ actualTaggedGoodQuestions I (actualPaddingCopies J T) J
          then f u else 0) /
        (actualTaggedGoodMass I (actualPaddingCopies J T) J : ℝ) ≤
        (4 / 3 : ℝ) * actualTaggedUniformMean I (actualPaddingCopies J T) J
          (fun u => if u ∈ actualTaggedGoodQuestions I (actualPaddingCopies J T) J
            then f u else 0) := by
          rw [div_eq_mul_inv]
          exact (by simpa [mul_comm] using hmul)
    _ ≤ (4 / 3 : ℝ) * actualTaggedUniformMean I (actualPaddingCopies J T) J f := by
      apply mul_le_mul_of_nonneg_left
      · unfold actualTaggedUniformMean
        apply div_le_div_of_nonneg_right
        · exact Finset.sum_le_sum (fun u hu => by split_ifs <;> linarith [hf u])
        · positivity
      · norm_num

theorem actualTaggedGoodMean_le_two_mul_uniformMean_of_nonneg
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m)
    (f : (Fin J → Fin (actualPaddingCopies J T) × I.RowId) → ℝ)
    (hf : ∀ u, 0 ≤ f u) :
    actualTaggedGoodMean I (actualPaddingCopies J T) J f ≤
      2 * actualTaggedUniformMean I (actualPaddingCopies J T) J f := by
  have hfour := actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg
    I J T hT hm f hf
  have huniform_nonneg : 0 ≤ actualTaggedUniformMean I
      (actualPaddingCopies J T) J f := by
    unfold actualTaggedUniformMean
    apply div_nonneg
    · exact Finset.sum_nonneg (fun u hu => hf u)
    · positivity
  nlinarith

end
end PvNP.RealizableHardness.ActualQuestionMassBridge
