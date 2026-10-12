import PvNP.RealizableHardness.ActualOccurrenceAdviceLaw
import PvNP.RealizableHardness.ActualLocalQuestionLaw
import PvNP.RealizableHardness.ActualOriginalRealRowLaw

/-! Total local strategies on the original occurrence questions, their
literal acceptance score, and its exact eligible restriction. The raw
advice law keeps independent occurrence vectors even on repeated rows.
External source-NO strategy-domain binding remains separate. Uncompiled. -/
namespace PvNP.RealizableHardness.ActualTotalOrderedStrategy

open scoped BigOperators
open ActualOccurrenceAllocation ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedOrderedQuestionSourceBridge ActualQuestionMassBridge ActualTaggedRowDeletion
open ActualVisibleQuestionCompletion ActualVisibleAmbientLadder ActualFunctionalAssignmentAcceptance
open ActualOrderedDeletionLaw ActualOccurrenceAdviceLaw ActualLocalAssignmentStrategies
open ActualLocalQuestionLaw ActualOriginalRealRowLaw ActualOriginalOrderedRowLaw
open ActualPrivateAssignmentLaw ActualFiniteLaw ActualNumericSourceHeight
open TripleRestrictionRank GrassmannIncidence VectorAdvice SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)

def sumRawVector {J : Nat} (v : Fin J → TaggedAmbient I copies) : TaggedAmbient I copies :=
  ∑ j, v j

/-- Only the ordered equations and the first prover's received vectors are
inputs. The hidden deletion draw and visible sets are absent. -/
def totalFirstLaw {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (u : Fin J → TaggedRow I copies)
    (v : Fin (numericRankThreshold m) → Fin J → TaggedAmbient I copies) :
    FiniteLaw (TaggedAmbient I copies) :=
  if hu : GoodOrderedQuestion (taggedSource I copies).support u then
    let U := orderedToGoodU I copies J ⟨u, hu⟩
    if hv : ∀ i, sumRawVector I copies (v i) ∈ OriginalSpace I copies U then
      originalLocalLaw I copies m a U T choice
        (fun i => ⟨sumRawVector I copies (v i), hv i⟩)
    else dirac 0
  else dirac 0

/-- The second prover uses its visible occurrence sets and received vectors.
It has no original equation tuple or eligibility test. -/
def totalSecondLaw {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (X : Fin J → Finset (TaggedVar I copies))
    (v : Fin (numericRankThreshold m) → Fin J → TaggedAmbient I copies) :
    FiniteLaw (TaggedAmbient I copies) :=
  if hv : ∀ i, sumRawVector I copies (v i) ∈
      visibleCoordinateSpace I copies (occurrenceUnion I copies X) then
    visibleLocalLaw I copies m a T choice C (occurrenceUnion I copies X)
      (fun i => ⟨sumRawVector I copies (v i), hv i⟩)
  else dirac 0

theorem total_first_law_good {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (u : TaggedOrderedGood I copies J)
    (v : Fin (numericRankThreshold m) → Fin J → TaggedAmbient I copies)
    (w : Fin (numericRankThreshold m) → OriginalSpace I copies (orderedToGoodU I copies J u))
    (hw : ∀ i, sumRawVector I copies (v i) = (w i).val) :
    totalFirstLaw I copies m a T choice u.val v =
      originalLocalLaw I copies m a (orderedToGoodU I copies J u) T choice w := by
  have hv : ∀ i, sumRawVector I copies (v i) ∈
      OriginalSpace I copies (orderedToGoodU I copies J u) := by
    intro i
    rw [hw i]
    exact (w i).property
  simp only [totalFirstLaw, dif_pos u.property, dif_pos hv]
  congr 1
  funext i
  exact Subtype.ext (hw i)

theorem total_second_law_supported {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (X : Fin J → Finset (TaggedVar I copies))
    (v : Fin (numericRankThreshold m) → Fin J → TaggedAmbient I copies)
    (Y : Finset (TaggedVar I copies)) (hXY : occurrenceUnion I copies X = Y)
    (w : Fin (numericRankThreshold m) → visibleCoordinateSpace I copies Y)
    (hw : ∀ i, sumRawVector I copies (v i) = (w i).val) :
    totalSecondLaw I copies m a T choice C X v =
      visibleLocalLaw I copies m a T choice C Y w := by
  subst Y
  have hv : ∀ i, sumRawVector I copies (v i) ∈
      visibleCoordinateSpace I copies (occurrenceUnion I copies X) := by
    intro i
    rw [hw i]
    exact (w i).property
  simp only [totalSecondLaw, dif_pos hv]
  congr 1
  funext i
  exact Subtype.ext (hw i)

/-- Literal independent private outputs tested against every original
equation occurrence and every visible variable. -/
def orderedTupleScore {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (u : Fin J → TaggedRow I copies) (d : Draw J)
    (v : Fin (numericRankThreshold m) →
      OccurrenceAdvice I copies (orderedVisibleBlock I copies u d)) : Rat :=
  eventMass (independentProduct
    (totalFirstLaw I copies m a T choice u (fun i j => (v i j).val))
    (totalSecondLaw I copies m a T choice C (orderedVisibleBlock I copies u d)
      (fun i j => (v i j).val)))
    (Finset.univ.filter fun p =>
      orderedAssignmentAccepts I copies u (orderedVisibleUnion I copies u d) p.1 p.2)

theorem ordered_tuple_score_nonneg {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (u : Fin J → TaggedRow I copies) (d : Draw J)
    (v : Fin (numericRankThreshold m) →
      OccurrenceAdvice I copies (orderedVisibleBlock I copies u d)) :
    0 ≤ orderedTupleScore I copies m a T choice C u d v := by
  unfold orderedTupleScore eventMass
  exact Finset.sum_nonneg (fun p _ => (independentProduct _ _).nonneg p)

theorem ordered_tuple_score_actual {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (u : TaggedOrderedGood I copies J) (d : Draw J)
    (v : Fin (numericRankThreshold m) →
      OccurrenceAdvice I copies (orderedVisibleBlock I copies u.val d)) :
    orderedTupleScore I copies m a T choice C u.val d v =
      localAssignmentScore I copies m a (orderedToGoodU I copies J u) T choice C
        (orderedDrawEquiv I copies u d)
        (fun i => orderedOccurrenceEquiv I copies u d (v i)) := by
  have hfirst := total_first_law_good I copies m a T choice u
    (fun i j => (v i j).val)
    (fun i => (orderedOccurrenceEquiv I copies u d (v i)).val) (fun _ => rfl)
  have hsecond := total_second_law_supported I copies m a T choice C
    (orderedVisibleBlock I copies u.val d) (fun i j => (v i j).val)
    (retainedVariables I copies J (orderedToGoodU I copies J u) (orderedDrawEquiv I copies u d))
    (ordered_visible_union_actual I copies u d)
    (fun i => retainedVisibleEquiv I copies J (orderedToGoodU I copies J u)
      (orderedDrawEquiv I copies u d) (orderedOccurrenceEquiv I copies u d (v i)))
    (fun _ => rfl)
  unfold orderedTupleScore localAssignmentScore
  rw [hfirst, hsecond, ordered_visible_union_actual]
  congr 1
  apply Finset.ext
  intro p
  simp only [assignmentAcceptanceEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ordered_acceptance_actual I copies u _ p.1 p.2

/-- Original independent occurrence deletions and independent uniform full
advice vectors. No eligibility condition changes either sampling law. -/
def orderedQuestionScore {A m h : Nat} (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat)
    (u : Fin (blocks A h) → TaggedRow I copies) : Real :=
  ∑ d : Draw (blocks A h), (prior (beta A h) d : Real) *
    ∑ v : Fin (numericRankThreshold m) →
      OccurrenceAdvice I copies (orderedVisibleBlock I copies u d),
      uniformArray v * (orderedTupleScore I copies m a T choice C u d v : Real)

theorem ordered_question_score_nonneg {A m h : Nat} (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat)
    (u : Fin (blocks A h) → TaggedRow I copies) :
    0 ≤ orderedQuestionScore I copies a T choice C u := by
  unfold orderedQuestionScore
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg
  · exact_mod_cast drawMass_nonneg (beta A h) (beta_nonneg A h) (beta_le_one A h) d
  · apply Finset.sum_nonneg
    intro v _
    apply mul_nonneg (by unfold uniformArray; positivity)
    exact_mod_cast ordered_tuple_score_nonneg I copies m a T choice C u d v

theorem ordered_question_score_good {A m h : Nat} (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat)
    (u : TaggedOrderedGood I copies (blocks A h)) :
    orderedQuestionScore I copies a T choice C u.val =
      actualLocalQuestionScore I copies (orderedToGoodU I copies (blocks A h) u) a T choice C := by
  unfold orderedQuestionScore actualLocalQuestionScore
  simp_rw [ordered_tuple_score_actual]
  calc
    _ = ∑ d : Draw (blocks A h), (prior (beta A h) d : Real) *
        ∑ w : Fin (numericRankThreshold m) → actualRetained I copies
          (orderedToGoodU I copies (blocks A h) u) (orderedDrawEquiv I copies u d),
          uniformArray w * (localAssignmentScore I copies m a
            (orderedToGoodU I copies (blocks A h) u) T choice C
              (orderedDrawEquiv I copies u d) w : Real) := by
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      exact ordered_occurrence_tuple_mean I copies u d
        (fun w => (localAssignmentScore I copies m a
          (orderedToGoodU I copies (blocks A h) u) T choice C
            (orderedDrawEquiv I copies u d) w : Real))
    _ = _ := ordered_draw_real_score_transport I copies u (beta A h)
      (fun s => ∑ w : Fin (numericRankThreshold m) → actualRetained I copies
        (orderedToGoodU I copies (blocks A h) u) s,
        uniformArray w * (localAssignmentScore I copies m a
          (orderedToGoodU I copies (blocks A h) u) T choice C s w : Real))

/-- The actual raw strategy proves the domination needed by the iid law;
the desired game probability is not a premise. -/
theorem eligible_actual_score_le_ordered {A m h : Nat} (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat)
    (u : Fin (blocks A h) → TaggedRow I copies) :
    eligibleRealScore I copies (blocks A h)
      (fun U => actualLocalQuestionScore I copies U a T choice C) u ≤
        orderedQuestionScore I copies a T choice C u := by
  by_cases hu : GoodOrderedQuestion (taggedSource I copies).support u
  · simp only [eligibleRealScore, dif_pos hu]
    exact (ordered_question_score_good I copies a T choice C ⟨u, hu⟩).ge
  · simp only [eligibleRealScore, dif_neg hu]
    exact ordered_question_score_nonneg I copies a T choice C u

/-- Return to the original unconditioned iid tuple law with its exact
eligibility factor, for these concrete total local strategies. -/
theorem actual_original_iid_mean_lower {A m h : Nat}
    [Nonempty (TaggedGoodU I copies (blocks A h))]
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    (ActualTaggedQuestionRetainedMass.actualTaggedGoodMass I copies (blocks A h) : Real) *
      (∑ U : TaggedGoodU I copies (blocks A h),
        ((uniformLaw (TaggedGoodU I copies (blocks A h))).mass U : Real) *
          actualLocalQuestionScore I copies U a T choice C) ≤
      ∑ u : Fin (blocks A h) → TaggedRow I copies,
        (iidOrderedMass I copies (blocks A h) u : Real) *
          orderedQuestionScore I copies a T choice C u := by
  exact iid_real_score_lower_of_eligible_domination I copies (blocks A h)
    (fun U => actualLocalQuestionScore I copies U a T choice C)
    (orderedQuestionScore I copies a T choice C)
    (eligible_actual_score_le_ordered I copies a T choice C)

end
end PvNP.RealizableHardness.ActualTotalOrderedStrategy
