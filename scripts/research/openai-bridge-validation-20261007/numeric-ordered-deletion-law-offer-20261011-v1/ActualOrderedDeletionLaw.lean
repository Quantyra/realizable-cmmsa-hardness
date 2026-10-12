import PvNP.RealizableHardness.ActualLocalAssignmentStrategies

/-! Original ordered occurrences, their independent deletion law, and the
exact eligible row-set representation. Advice on repeated occurrences is
not merged probabilistically. The complete game law remains separate.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualOrderedDeletionLaw

open scoped BigOperators
open ActualOccurrenceAllocation ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedOrderedQuestionSourceBridge ActualQuestionMassBridge
open ActualTaggedRowDeletion ActualVisibleQuestionCompletion ActualPrivateAssignmentLaw
open ActualStarQuestionSupport TripleRestrictionRank GrassmannIncidence

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)

/-- The actual supplied ordering, rather than a chosen canonical ordering. -/
def orderedRowEquiv {J : Nat} (u : TaggedOrderedGood I copies J) :
    Fin J ≃ ↥(orderedToGoodU I copies J u).1 :=
  Equiv.ofBijective
    (fun j => ⟨u.1 j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    ⟨by
      intro i j hij
      exact u.2.1 (congrArg Subtype.val hij), by
      intro e
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp e.2
      exact ⟨j, Subtype.ext hj⟩⟩

theorem orderedRowEquiv_apply {J : Nat} (u : TaggedOrderedGood I copies J) (j : Fin J) :
    (orderedRowEquiv I copies u j).val = u.1 j := rfl

/-- Relabel independently sampled occurrence choices by their actual rows. -/
def orderedDrawEquiv {J : Nat} (u : TaggedOrderedGood I copies J) :
    Draw J ≃ ActualRowDraw I copies (orderedToGoodU I copies J u) where
  toFun d e := d ((orderedRowEquiv I copies u).symm e)
  invFun s j := s (orderedRowEquiv I copies u j)
  left_inv := by intro d; funext j; simp
  right_inv := by intro s; funext e; simp

theorem orderedDrawEquiv_apply_row {J : Nat} (u : TaggedOrderedGood I copies J)
    (d : Draw J) (j : Fin J) :
    orderedDrawEquiv I copies u d (orderedRowEquiv I copies u j) = d j := by
  simp only [orderedDrawEquiv, Equiv.symm_apply_apply]

/-- Every original independent block probability is retained exactly. -/
theorem ordered_draw_mass {J : Nat} (u : TaggedOrderedGood I copies J)
    (b : Rat) (d : Draw J) :
    actualRowDrawMass I copies (orderedToGoodU I copies J u) b
      (orderedDrawEquiv I copies u d) = prior b d := by
  have hp := Equiv.prod_comp (orderedRowEquiv I copies u)
    (fun e => blockMass b (orderedDrawEquiv I copies u d e))
  simpa only [orderedDrawEquiv_apply_row, actualRowDrawMass, prior,
    FiniteSampling.trialMass] using hp.symm

theorem ordered_draw_real_score_transport {J : Nat} (u : TaggedOrderedGood I copies J)
    (b : Rat) (f : ActualRowDraw I copies (orderedToGoodU I copies J u) → Real) :
    (∑ d : Draw J, (prior b d : Real) * f (orderedDrawEquiv I copies u d)) =
      ∑ s : ActualRowDraw I copies (orderedToGoodU I copies J u),
        (actualRowDrawMass I copies (orderedToGoodU I copies J u) b s : Real) * f s := by
  apply Fintype.sum_equiv (orderedDrawEquiv I copies u)
  intro d
  rw [ordered_draw_mass]

/-- Visible variables in one original occurrence, defined also for repeated
or otherwise ineligible tuples. -/
def orderedVisibleBlock {J : Nat} (u : Fin J → TaggedRow I copies) (d : Draw J)
    (j : Fin J) : Finset (TaggedVar I copies) :=
  Finset.univ.filter fun x => ∃ i : Fin 3,
    (taggedSource I copies).row (u j) i = x ∧ (d j = none ∨ d j = some i)

def orderedVisibleUnion {J : Nat} (u : Fin J → TaggedRow I copies) (d : Draw J) :
    Finset (TaggedVar I copies) :=
  Finset.univ.biUnion (orderedVisibleBlock I copies u d)

theorem ordered_visible_block_subset {J : Nat} (u : Fin J → TaggedRow I copies)
    (d : Draw J) (j : Fin J) :
    orderedVisibleBlock I copies u d j ⊆ (taggedSource I copies).support (u j) := by
  intro x hx
  obtain ⟨i, hi, _⟩ := (Finset.mem_filter.mp hx).2
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

/-- Both directions identify the retained union with the actual carrier. -/
theorem ordered_visible_union_actual {J : Nat} (u : TaggedOrderedGood I copies J)
    (d : Draw J) :
    orderedVisibleUnion I copies u.1 d =
      retainedVariables I copies J (orderedToGoodU I copies J u)
        (orderedDrawEquiv I copies u d) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, hi, hkeep⟩ := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, orderedRowEquiv I copies u j, i, hi, ?_⟩
    simpa only [orderedDrawEquiv_apply_row] using hkeep
  · intro hx
    obtain ⟨e, i, hi, hkeep⟩ := (Finset.mem_filter.mp hx).2
    let j := (orderedRowEquiv I copies u).symm e
    have he : orderedRowEquiv I copies u j = e :=
      (orderedRowEquiv I copies u).apply_symm_apply e
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨Finset.mem_univ x, i, ?_, ?_⟩⟩
    · simpa only [← he, orderedRowEquiv_apply] using hi
    · simpa only [orderedDrawEquiv, j] using hkeep

/-- Disjointness is used only on the eligible branch. -/
theorem ordered_visible_blocks_disjoint {J : Nat} (u : TaggedOrderedGood I copies J)
    (d : Draw J) :
    Pairwise (fun i j => Disjoint (orderedVisibleBlock I copies u.1 d i)
      (orderedVisibleBlock I copies u.1 d j)) := by
  intro i j hij
  have hi : u.1 i ∈ (orderedToGoodU I copies J u).1 :=
    (orderedRowEquiv I copies u i).2
  have hj : u.1 j ∈ (orderedToGoodU I copies J u).1 :=
    (orderedRowEquiv I copies u j).2
  have hne : u.1 i ≠ u.1 j := fun heq => hij (u.2.1 heq)
  exact ((orderedToGoodU I copies J u).2.1.1 hi hj hne).mono
    (ordered_visible_block_subset I copies u.1 d i)
    (ordered_visible_block_subset I copies u.1 d j)

/-- Original occurrence equations and agreement on the retained union. -/
def orderedAssignmentAccepts {J : Nat} (u : Fin J → TaggedRow I copies)
    (X : Finset (TaggedVar I copies)) (first second : TaggedAmbient I copies) : Prop :=
  (∀ j : Fin J,
    first ((taggedSource I copies).row (u j) 0) +
      first ((taggedSource I copies).row (u j) 1) +
      first ((taggedSource I copies).row (u j) 2) = (taggedSource I copies).rhs (u j)) ∧
    ∀ x, x ∈ X → first x = second x

theorem ordered_acceptance_actual {J : Nat} (u : TaggedOrderedGood I copies J)
    (X : Finset (TaggedVar I copies)) (first second : TaggedAmbient I copies) :
    orderedAssignmentAccepts I copies u.1 X first second ↔
      assignmentAccepts I copies (orderedToGoodU I copies J u) X first second := by
  constructor
  · rintro ⟨heq, hagree⟩
    refine ⟨?_, hagree⟩
    intro row hrow
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hrow
    exact heq j
  · rintro ⟨heq, hagree⟩
    refine ⟨?_, hagree⟩
    intro j
    exact heq (u.1 j) (orderedRowEquiv I copies u j).2

end
end PvNP.RealizableHardness.ActualOrderedDeletionLaw
