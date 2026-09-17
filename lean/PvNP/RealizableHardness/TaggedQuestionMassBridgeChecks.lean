import PvNP.RealizableHardness.TaggedQuestionMassBridge

namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open Finite3LinSource
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check taggedTupleEquiv
#check tagProjection
#check baseProjection
#check taggedTupleEquiv_apply
#check taggedTupleEquiv_symm_apply
#check taggedTuple_card
#check baseProjectionEventEquiv
#check baseProjection_event_card
#check taggedCopy_rowConflict_iff
#check taggedCopy_not_good_iff
#check taggedConflictFibreEquiv
#check tagged_bad_ordered_question_count_le
#check tagged_bad_ordered_question_count_mul_rowCard_le
#check tagged_bad_ordered_question_uniform_mass_le

#print axioms taggedTupleEquiv
#print axioms tagProjection
#print axioms baseProjection
#print axioms taggedTupleEquiv_apply
#print axioms taggedTupleEquiv_symm_apply
#print axioms taggedTuple_card
#print axioms baseProjectionEventEquiv
#print axioms baseProjection_event_card
#print axioms taggedCopy_rowConflict_iff
#print axioms taggedCopy_not_good_iff
#print axioms taggedConflictFibreEquiv
#print axioms tagged_bad_ordered_question_count_le
#print axioms tagged_bad_ordered_question_count_mul_rowCard_le
#print axioms tagged_bad_ordered_question_uniform_mass_le

def singletonBaseEvent : Finset (Fin 2 → Fin 3) :=
  {fun _ => (0 : Fin 3)}

example :
    ((Finset.univ : Finset (Fin 2 → Fin 2 × Fin 3)).filter
      (fun u => baseProjection u ∈ singletonBaseEvent)).card = 4 := by
  rw [baseProjection_event_card]
  decide

example : Fintype.card (Fin 2 → Fin 2 × Fin 3) = 36 := by
  decide

def oneRowSource : Finite3LinSource Unit (Fin 3) where
  row _ i := i
  rhs _ := 0
  row_injective _ := Function.injective_id

example :
    ((Finset.univ : Finset (Fin 2 → Fin 2 × Unit)).filter
      (fun u => ¬ GoodOrderedQuestion (oneRowSource.taggedCopy 2).support u)).card = 2 := by
  let u0 : Fin 2 → Fin 2 × Unit := fun _ => (0, ())
  let u1 : Fin 2 → Fin 2 × Unit := fun _ => (1, ())
  have hbad (u : Fin 2 → Fin 2 × Unit) :
      ¬ GoodOrderedQuestion (oneRowSource.taggedCopy 2).support u ↔
        (u 0).1 = (u 1).1 := by
    rw [taggedCopy_not_good_iff]
    constructor
    · rintro ⟨i, j, hij, htag, hconflict⟩
      fin_cases i <;> fin_cases j <;> simp_all
    · intro htag
      refine ⟨0, 1, by decide, htag, ?_⟩
      simp [rowConflict]
  have hset :
      (Finset.univ : Finset (Fin 2 → Fin 2 × Unit)).filter
          (fun u => ¬ GoodOrderedQuestion (oneRowSource.taggedCopy 2).support u) =
        {u0, u1} := by
    ext u
    rw [Finset.mem_filter]
    rw [hbad]
    simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro htag
      have h0 : (u 0).1 = 0 ∨ (u 0).1 = 1 := by
        rcases Fin.eq_zero_or_eq_succ ((u 0).1) with h | ⟨j, h⟩
        · exact Or.inl h
        · right
          have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
          simpa [hj] using h
      have pair_eq_zero (x : Fin 2 × Unit) (hx : x.1 = 0) :
          x = (0, ()) := by
        apply Prod.ext
        · exact hx
        · exact Subsingleton.elim _ _
      have pair_eq_one (x : Fin 2 × Unit) (hx : x.1 = 1) :
          x = (1, ()) := by
        apply Prod.ext
        · exact hx
        · exact Subsingleton.elim _ _
      rcases h0 with h0 | h0
      · left
        funext i
        fin_cases i
        · exact pair_eq_zero (u 0) h0
        · have h1 : (u 1).1 = 0 := htag ▸ h0
          exact pair_eq_zero (u 1) h1
      · right
        funext i
        fin_cases i
        · exact pair_eq_one (u 0) h0
        · have h1 : (u 1).1 = 1 := htag ▸ h0
          exact pair_eq_one (u 1) h1
    · rintro (rfl | rfl) <;> simp [u0, u1]
  have hne : u0 ≠ u1 := by
    intro h
    have hz := congrFun h 0
    simp [u0, u1] at hz
  rw [hset]
  simp [hne]

example :
    (((Finset.univ : Finset (Fin 2 → Fin 2 × Unit)).filter
      (fun u => ¬ GoodOrderedQuestion (oneRowSource.taggedCopy 2).support u)).card : ℚ) /
        (Fintype.card (Fin 2 → Fin 2 × Unit) : ℚ) ≤
      (2 * (2 - 1) * 1 : ℚ) / (2 * Fintype.card Unit : ℚ) := by
  apply tagged_bad_ordered_question_uniform_mass_le oneRowSource 2 2 1
    (by decide) (by decide)
  intro q
  cases q
  have hfilter :
      (Finset.univ : Finset Unit).filter
          (rowConflict oneRowSource.support ()) = Finset.univ := by
    ext x
    simp [rowConflict]
  rw [hfilter]
  simp

end
end PvNP.RealizableHardness.ActualQuestionMassBridge
