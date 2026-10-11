import PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge

/-! The exact eligibility charge for returning from good original row sets
to the original iid ordered-row experiment. Scores remain explicit; this
does not construct the complete outer strategy. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualOriginalOrderedRowLaw

open scoped BigOperators
open ActualFiniteLaw ActualOccurrenceAllocation ActualQuestionMassBridge
open ActualTaggedFixedCenterGeometry ActualTaggedConcreteStarLaw
open ActualTaggedOrderedQuestionSourceBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N m : Nat} (I : Instance N m) (copies J : Nat)

/-- Original ordered rows are independent and uniform, before eligibility. -/
def iidOrderedMass (_u : Fin J → TaggedRow I copies) : ℚ :=
  1 / Fintype.card (Fin J → TaggedRow I copies)

theorem iidOrderedMass_eq_product (u : Fin J → TaggedRow I copies) :
    iidOrderedMass I copies J u =
      ∏ _i : Fin J, (1 : ℚ) / (copies * I.rows.length : Nat) := by
  have hc : Fintype.card (TaggedRow I copies) = copies * I.rows.length :=
    actual_tagged_row_card I copies
  simp [iidOrderedMass, Fintype.card_fun, hc, div_pow]

theorem iidOrderedMass_normalized (hcopies : 0 < copies) (hm : 0 < m) :
    ∑ u : Fin J → TaggedRow I copies, iidOrderedMass I copies J u = 1 := by
  have hp := actual_tagged_total_question_count_pos I copies J hcopies hm
  have hn : (Fintype.card (Fin J → TaggedRow I copies) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hp
  simp [iidOrderedMass, hn]

/-- Zero extension keeps the eligibility cost in the original experiment. -/
def eligibleScore (s : TaggedGoodU I copies J → ℚ)
    (u : Fin J → TaggedRow I copies) : ℚ :=
  if hu : GoodOrderedQuestion (taggedSource I copies).support u then
    s (orderedToGoodU I copies J ⟨u, hu⟩)
  else 0

theorem eligibleScore_of_good (s : TaggedGoodU I copies J → ℚ)
    (u : TaggedOrderedGood I copies J) :
    eligibleScore I copies J s u.1 = s (orderedToGoodU I copies J u) := by
  simp [eligibleScore, u.2]

/-- The already proved exact pushforward transports every finite score. -/
theorem orderedGood_score_mean [Nonempty (TaggedGoodU I copies J)]
    (s : TaggedGoodU I copies J → ℚ) :
    (∑ u : TaggedOrderedGood I copies J,
      (orderedGoodLaw I copies J).mass u * s (orderedToGoodU I copies J u)) =
    ∑ U : TaggedGoodU I copies J,
      (uniformLaw (TaggedGoodU I copies J)).mass U * s U := by
  rw [← orderedGood_pushforward I copies J]
  simp only [pushforward_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [ite_mul]

/-- Exact first-question law identity, with no conditioned-law substitution. -/
theorem iid_eligible_score_eq_goodMass_mul_mean
    [Nonempty (TaggedGoodU I copies J)]
    (s : TaggedGoodU I copies J → ℚ) :
    (∑ u : Fin J → TaggedRow I copies,
      iidOrderedMass I copies J u * eligibleScore I copies J s u) =
    actualTaggedGoodMass I copies J *
      ∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U * s U := by
  have hcard : (actualTaggedGoodQuestions I copies J).card =
      Fintype.card (TaggedOrderedGood I copies J) := by
    rw [TaggedOrderedGood, Fintype.card_subtype]
    rfl
  have hnonzero : (Fintype.card (TaggedOrderedGood I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (TaggedOrderedGood I copies J) ≠ 0)
  letI : Nonempty (Fin J → TaggedRow I copies) :=
    ⟨(Classical.choice (inferInstance : Nonempty (TaggedOrderedGood I copies J))).1⟩
  have htotal : (Fintype.card (Fin J → TaggedRow I copies) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Fin J → TaggedRow I copies) ≠ 0)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (GoodOrderedQuestion (taggedSource I copies).support)
    (eligibleScore I copies J s)
  have hsum : (∑ u : Fin J → TaggedRow I copies, eligibleScore I copies J s u) =
      ∑ u : TaggedOrderedGood I copies J, s (orderedToGoodU I copies J u) := by
    have hbad : (∑ u : {u : Fin J → TaggedRow I copies //
        ¬ GoodOrderedQuestion (taggedSource I copies).support u},
        eligibleScore I copies J s u.1) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      simp [eligibleScore, u.2]
    rw [hbad, add_zero] at hsplit
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro u _
    exact eligibleScore_of_good I copies J s u
  rw [← orderedGood_score_mean I copies J s]
  simp only [iidOrderedMass, orderedGoodLaw, uniformLaw_apply, ← Finset.mul_sum]
  rw [hsum]
  unfold actualTaggedGoodMass
  rw [hcard]
  field_simp [hnonzero, htotal] <;> ring

/-- A genuine total-strategy score can be compared pointwise to the zero
extension. The strategy and this comparison still need actual instantiation. -/
theorem iid_score_lower_of_eligible_domination
    [Nonempty (TaggedGoodU I copies J)]
    (s : TaggedGoodU I copies J → ℚ)
    (score : (Fin J → TaggedRow I copies) → ℚ)
    (hscore : ∀ u, eligibleScore I copies J s u ≤ score u) :
    actualTaggedGoodMass I copies J *
      (∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U * s U) ≤
      ∑ u : Fin J → TaggedRow I copies, iidOrderedMass I copies J u * score u := by
  rw [← iid_eligible_score_eq_goodMass_mul_mean I copies J s]
  apply Finset.sum_le_sum
  intro u _
  exact mul_le_mul_of_nonneg_left (hscore u) (by
    unfold iidOrderedMass
    positivity)

/-- At the existing padding, returning to the iid question law costs at
most the proved factor three quarters. -/
theorem padded_iid_score_lower (T : Nat) (hT : 4 ≤ T) (hm : 0 < m)
    [Nonempty (TaggedGoodU I (actualPaddingCopies J T) J)]
    (s : TaggedGoodU I (actualPaddingCopies J T) J → ℚ)
    (score : (Fin J → TaggedRow I (actualPaddingCopies J T)) → ℚ)
    (hscore : ∀ u, eligibleScore I (actualPaddingCopies J T) J s u ≤ score u)
    (B : ℚ) (hB : 0 ≤ B)
    (hmean : B ≤ ∑ U : TaggedGoodU I (actualPaddingCopies J T) J,
      (uniformLaw (TaggedGoodU I (actualPaddingCopies J T) J)).mass U * s U) :
    (3 : ℚ) / 4 * B ≤
      ∑ u : Fin J → TaggedRow I (actualPaddingCopies J T),
        iidOrderedMass I (actualPaddingCopies J T) J u * score u := by
  have hg := actual_tagged_good_mass_ge_three_quarters I J T hT hm
  have hdom := iid_score_lower_of_eligible_domination I
    (actualPaddingCopies J T) J s score hscore
  have hnonneg : (0 : ℚ) ≤ actualTaggedGoodMass I (actualPaddingCopies J T) J := by
    linarith
  have h1 := mul_le_mul_of_nonneg_right hg hB
  have h2 := mul_le_mul_of_nonneg_left hmean hnonneg
  exact h1.trans (h2.trans hdom)

end
end PvNP.RealizableHardness.ActualOriginalOrderedRowLaw
