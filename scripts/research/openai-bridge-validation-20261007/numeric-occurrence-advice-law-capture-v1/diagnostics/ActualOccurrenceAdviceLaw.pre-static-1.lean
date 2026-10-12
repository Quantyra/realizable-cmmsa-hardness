import PvNP.RealizableHardness.ActualOrderedDeletionLaw

/-! Advice is a product of the individual occurrence coordinate spaces.
Only pairwise disjoint visible blocks admit the uniform-union equivalence.
Repeated occurrences retain their full product law. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualOccurrenceAdviceLaw

open scoped BigOperators
open ActualOccurrenceAllocation ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualVisibleQuestionCompletion ActualSharedAdviceSpans ActualOrderedDeletionLaw
open ActualTaggedOrderedQuestionSourceBridge ActualTaggedRowDeletion
open ActualVisibleAmbientLadder ActualFunctionalAssignmentAcceptance VectorAdvice

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)

def occurrenceUnion {J : Nat} (X : Fin J → Finset (TaggedVar I copies)) :
    Finset (TaggedVar I copies) := Finset.univ.biUnion X

abbrev OccurrenceAdvice {J : Nat} (X : Fin J → Finset (TaggedVar I copies)) :=
  (j : Fin J) → visibleCoordinateSpace I copies (X j)

/-- Deterministic local preprocessing, defined even when blocks overlap. -/
def sumOccurrence {J : Nat} (X : Fin J → Finset (TaggedVar I copies))
    (v : OccurrenceAdvice I copies X) :
    visibleCoordinateSpace I copies (occurrenceUnion I copies X) :=
  ⟨∑ j, (v j).val, by
    intro x hx
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply (v j).property x
    intro hj
    exact hx (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)⟩

/-- Each occurrence reads only its own coordinates. -/
def restrictOccurrence {J : Nat} (X : Fin J → Finset (TaggedVar I copies))
    (v : TaggedAmbient I copies) : OccurrenceAdvice I copies X :=
  fun j => ⟨fun x => if x ∈ X j then v x else 0, by intro x hx; simp [hx]⟩

theorem restrict_sumOccurrence {J : Nat} (X : Fin J → Finset (TaggedVar I copies))
    (hX : Pairwise (fun i j => Disjoint (X i) (X j)))
    (v : OccurrenceAdvice I copies X) :
    restrictOccurrence I copies X (sumOccurrence I copies X v).val = v := by
  funext j
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ X j
  · change (if x ∈ X j then (∑ k, (v k).val) x else 0) = (v j).val x
    rw [if_pos hx]
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_single j
    · intro k _ hkj
      apply (v k).property x
      intro hk
      exact Finset.disjoint_left.mp (hX hkj) hk hx
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  · change (if x ∈ X j then _ else 0) = (v j).val x
    rw [if_neg hx, (v j).property x hx]

theorem sumOccurrence_restrict {J : Nat} (X : Fin J → Finset (TaggedVar I copies))
    (hX : Pairwise (fun i j => Disjoint (X i) (X j)))
    (v : visibleCoordinateSpace I copies (occurrenceUnion I copies X)) :
    sumOccurrence I copies X (restrictOccurrence I copies X v.val) = v := by
  apply Subtype.ext
  funext x
  change (∑ j, if x ∈ X j then v.val x else 0) = v.val x
  by_cases hx : x ∈ occurrenceUnion I copies X
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    rw [Finset.sum_eq_single j]
    · exact if_pos hj
    · intro k _ hkj
      have hk : x ∉ X k := fun hk => Finset.disjoint_left.mp (hX hkj) hk hj
      exact if_neg hk
    · intro hj'
      exact False.elim (hj' (Finset.mem_univ j))
  · rw [v.property x hx]
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro hj
    exact hx (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)

/-- Disjointness, not eligibility conditioning in the sampling law, is the
precise premise for this carrier equivalence. -/
def occurrenceSumEquiv {J : Nat} (X : Fin J → Finset (TaggedVar I copies))
    (hX : Pairwise (fun i j => Disjoint (X i) (X j))) :
    OccurrenceAdvice I copies X ≃ₗ[ZMod 2]
      visibleCoordinateSpace I copies (occurrenceUnion I copies X) where
  toFun := sumOccurrence I copies X
  invFun v := restrictOccurrence I copies X v.val
  left_inv := restrict_sumOccurrence I copies X hX
  right_inv := sumOccurrence_restrict I copies X hX
  map_add' := by
    intro v w
    apply Subtype.ext
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c v
    apply Subtype.ext
    exact (Finset.smul_sum _ _ _).symm

theorem uniform_occurrence_tuple_mean {J r : Nat}
    (X : Fin J → Finset (TaggedVar I copies))
    (hX : Pairwise (fun i j => Disjoint (X i) (X j)))
    (F : (Fin r → visibleCoordinateSpace I copies (occurrenceUnion I copies X)) → Real) :
    (∑ v : Fin r → OccurrenceAdvice I copies X, uniformArray v *
      F (fun i => sumOccurrence I copies X (v i))) =
      ∑ w : Fin r → visibleCoordinateSpace I copies (occurrenceUnion I copies X),
        uniformArray w * F w := by
  exact uniform_tuple_mean_equiv (occurrenceSumEquiv I copies X hX) F

/-- On an eligible original ordering, summing the separate occurrence
vectors gives exactly the actual retained vector, with its original support. -/
def orderedOccurrenceToRetained {J : Nat} (u : TaggedOrderedGood I copies J)
    (d : TripleRestrictionRank.Draw J)
    (v : OccurrenceAdvice I copies (orderedVisibleBlock I copies u.val d)) :
    actualRetained I copies (orderedToGoodU I copies J u) (orderedDrawEquiv I copies u d) := by
  let w := sumOccurrence I copies (orderedVisibleBlock I copies u.val d) v
  have hw : w.val ∈ visibleCoordinateSpace I copies
      (retainedVariables I copies J (orderedToGoodU I copies J u)
        (orderedDrawEquiv I copies u d)) := by
    rw [← ordered_visible_union_actual]
    exact w.property
  have hu := visibleCoordinateSpace_le_question I copies J _
    (orderedToGoodU I copies J u)
    (retainedVariables_subset_support I copies J (orderedToGoodU I copies J u)
      (orderedDrawEquiv I copies u d)) hw
  refine ⟨⟨w.val, hu⟩, ?_⟩
  intro x hx
  apply hw x
  intro hmem
  exact hx (Finset.mem_filter.mp hmem).2

theorem orderedOccurrenceToRetained_global {J : Nat} (u : TaggedOrderedGood I copies J)
    (d : TripleRestrictionRank.Draw J)
    (v : OccurrenceAdvice I copies (orderedVisibleBlock I copies u.val d)) :
    (orderedOccurrenceToRetained I copies u d v).val.val = ∑ j, (v j).val := rfl

def orderedOccurrenceEquiv {J : Nat} (u : TaggedOrderedGood I copies J)
    (d : TripleRestrictionRank.Draw J) :
    OccurrenceAdvice I copies (orderedVisibleBlock I copies u.val d) ≃ₗ[ZMod 2]
      actualRetained I copies (orderedToGoodU I copies J u) (orderedDrawEquiv I copies u d) where
  toFun := orderedOccurrenceToRetained I copies u d
  invFun v := restrictOccurrence I copies (orderedVisibleBlock I copies u.val d) v.val.val
  left_inv := by
    intro v
    exact restrict_sumOccurrence I copies _ (ordered_visible_blocks_disjoint I copies u d) v
  right_inv := by
    intro v
    have hv : v.val.val ∈ visibleCoordinateSpace I copies
        (occurrenceUnion I copies (orderedVisibleBlock I copies u.val d)) := by
      change v.val.val ∈ visibleCoordinateSpace I copies (orderedVisibleUnion I copies u.val d)
      rw [ordered_visible_union_actual]
      exact (retainedVisibleEquiv I copies J (orderedToGoodU I copies J u)
        (orderedDrawEquiv I copies u d) v).property
    have heq := sumOccurrence_restrict I copies _
      (ordered_visible_blocks_disjoint I copies u d) ⟨v.val.val, hv⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val heq
  map_add' := by
    intro v w
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c v
    apply Subtype.ext
    apply Subtype.ext
    exact (Finset.smul_sum _ _ _).symm

theorem ordered_occurrence_tuple_mean {J r : Nat} (u : TaggedOrderedGood I copies J)
    (d : TripleRestrictionRank.Draw J)
    (F : (Fin r → actualRetained I copies (orderedToGoodU I copies J u)
      (orderedDrawEquiv I copies u d)) → Real) :
    (∑ v : Fin r → OccurrenceAdvice I copies (orderedVisibleBlock I copies u.val d),
      uniformArray v * F (fun i => orderedOccurrenceEquiv I copies u d (v i))) =
      ∑ w : Fin r → actualRetained I copies (orderedToGoodU I copies J u)
        (orderedDrawEquiv I copies u d), uniformArray w * F w := by
  exact uniform_tuple_mean_equiv (orderedOccurrenceEquiv I copies u d) F

end
end PvNP.RealizableHardness.ActualOccurrenceAdviceLaw
