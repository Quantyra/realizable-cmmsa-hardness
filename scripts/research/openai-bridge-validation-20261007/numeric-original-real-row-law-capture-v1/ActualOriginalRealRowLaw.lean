import PvNP.RealizableHardness.ActualOriginalOrderedRowLaw

/-! Exact real-score version of the original iid ordered-row identity.
The total original strategy and its domination must still be instantiated.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualOriginalRealRowLaw

open scoped BigOperators
open ActualOriginalOrderedRowLaw ActualFiniteLaw ActualOccurrenceAllocation
open ActualQuestionMassBridge ActualTaggedFixedCenterGeometry ActualTaggedConcreteStarLaw
open ActualTaggedOrderedQuestionSourceBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : Instance N rows) (copies J : Nat)

/-- Zero extension preserves the original eligibility probability. -/
def eligibleRealScore (f : TaggedGoodU I copies J → Real)
    (u : Fin J → TaggedRow I copies) : Real :=
  if hu : GoodOrderedQuestion (taggedSource I copies).support u then
    f (orderedToGoodU I copies J ⟨u, hu⟩)
  else 0

/-- The exact finite-law pushforward transports every real score. -/
theorem orderedGood_real_score_mean [Nonempty (TaggedGoodU I copies J)]
    (f : TaggedGoodU I copies J → Real) :
    (∑ u : TaggedOrderedGood I copies J,
      ((orderedGoodLaw I copies J).mass u : Real) * f (orderedToGoodU I copies J u)) =
      ∑ U : TaggedGoodU I copies J,
        ((uniformLaw (TaggedGoodU I copies J)).mass U : Real) * f U := by
  rw [← orderedGood_pushforward I copies J]
  simp only [pushforward_apply]
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [ite_mul]

/-- Exact unconditioned iid-row identity, with the eligibility factor
retained once and real-valued inner scores allowed. -/
theorem iid_eligible_real_score_eq_goodMass_mul_mean
    [Nonempty (TaggedGoodU I copies J)] (f : TaggedGoodU I copies J → Real) :
    (∑ u : Fin J → TaggedRow I copies,
      (iidOrderedMass I copies J u : Real) * eligibleRealScore I copies J f u) =
      (actualTaggedGoodMass I copies J : Real) *
        ∑ U : TaggedGoodU I copies J,
          ((uniformLaw (TaggedGoodU I copies J)).mass U : Real) * f U := by
  have hcard : (actualTaggedGoodQuestions I copies J).card =
      Fintype.card (TaggedOrderedGood I copies J) := by
    rw [TaggedOrderedGood, Fintype.card_subtype]
    rfl
  have hnonzero : (Fintype.card (TaggedOrderedGood I copies J) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (TaggedOrderedGood I copies J) ≠ 0)
  letI : Nonempty (Fin J → TaggedRow I copies) :=
    ⟨(Classical.choice (inferInstance : Nonempty (TaggedOrderedGood I copies J))).1⟩
  have htotal : (Fintype.card (Fin J → TaggedRow I copies) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin J → TaggedRow I copies) ≠ 0)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (GoodOrderedQuestion (taggedSource I copies).support) (eligibleRealScore I copies J f)
  have hsum : (∑ u : Fin J → TaggedRow I copies, eligibleRealScore I copies J f u) =
      ∑ u : TaggedOrderedGood I copies J, f (orderedToGoodU I copies J u) := by
    have hbad : (∑ u : {u : Fin J → TaggedRow I copies //
        ¬ GoodOrderedQuestion (taggedSource I copies).support u},
        eligibleRealScore I copies J f u.1) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      simp [eligibleRealScore, u.2]
    rw [hbad, add_zero] at hsplit
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro u _
    simp [eligibleRealScore, u.2]
  rw [← orderedGood_real_score_mean I copies J f]
  simp only [iidOrderedMass, orderedGoodLaw, uniformLaw_apply]
  push_cast
  simp only [← Finset.mul_sum]
  rw [hsum]
  unfold actualTaggedGoodMass
  push_cast
  rw [hcard]
  field_simp [hnonzero, htotal] <;> ring

/-- A concrete total original-row score can be compared without replacing
the iid law by a conditioned question law. Actual application is still needed. -/
theorem iid_real_score_lower_of_eligible_domination
    [Nonempty (TaggedGoodU I copies J)]
    (f : TaggedGoodU I copies J → Real)
    (score : (Fin J → TaggedRow I copies) → Real)
    (hscore : ∀ u, eligibleRealScore I copies J f u ≤ score u) :
    (actualTaggedGoodMass I copies J : Real) *
      (∑ U : TaggedGoodU I copies J,
        ((uniformLaw (TaggedGoodU I copies J)).mass U : Real) * f U) ≤
      ∑ u : Fin J → TaggedRow I copies, (iidOrderedMass I copies J u : Real) * score u := by
  rw [← iid_eligible_real_score_eq_goodMass_mul_mean I copies J f]
  apply Finset.sum_le_sum
  intro u _
  apply mul_le_mul_of_nonneg_left (hscore u)
  unfold iidOrderedMass
  positivity

/-- The proved padding eligibility bound supplies the conservative single
one-half factor used by the count-cost absorption. -/
theorem padded_iid_real_score_lower_half (T : Nat) (hT : 4 ≤ T) (hrows : 0 < rows)
    [Nonempty (TaggedGoodU I (actualPaddingCopies J T) J)]
    (f : TaggedGoodU I (actualPaddingCopies J T) J → Real)
    (score : (Fin J → TaggedRow I (actualPaddingCopies J T)) → Real)
    (hscore : ∀ u, eligibleRealScore I (actualPaddingCopies J T) J f u ≤ score u)
    (B : Real) (hB : 0 ≤ B)
    (hmean : B ≤ ∑ U : TaggedGoodU I (actualPaddingCopies J T) J,
      ((uniformLaw (TaggedGoodU I (actualPaddingCopies J T) J)).mass U : Real) * f U) :
    (1 : Real) / 2 * B ≤
      ∑ u : Fin J → TaggedRow I (actualPaddingCopies J T),
        (iidOrderedMass I (actualPaddingCopies J T) J u : Real) * score u := by
  have hgood : (3 : Real) / 4 ≤ (actualTaggedGoodMass I (actualPaddingCopies J T) J : Real) := by
    exact_mod_cast actual_tagged_good_mass_ge_three_quarters I J T hT hrows
  have hhalf : (1 : Real) / 2 ≤ (actualTaggedGoodMass I (actualPaddingCopies J T) J : Real) := by
    linarith
  have hnonneg : (0 : Real) ≤ (actualTaggedGoodMass I (actualPaddingCopies J T) J : Real) := by
    linarith
  have hdom := iid_real_score_lower_of_eligible_domination I
    (actualPaddingCopies J T) J f score hscore
  exact (mul_le_mul_of_nonneg_right hhalf hB).trans
    ((mul_le_mul_of_nonneg_left hmean hnonneg).trans hdom)

end
end PvNP.RealizableHardness.ActualOriginalRealRowLaw
