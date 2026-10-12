import PvNP.RealizableHardness.TaggedQuestionMassBridge

namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open ActualOccurrenceAllocation
open Finite3LinSource
open scoped BigOperators
set_option autoImplicit false
noncomputable section

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance actualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

local instance actualConflictDecidablePred {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (q : I.RowId) :
    DecidablePred (rowConflict (Finite3LinSource.ofActual I).support q) :=
  fun _ => Classical.propDecidable _

local instance actualTaggedBadDecidablePred {N m K J : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    DecidablePred (fun u : Fin J → Fin K × I.RowId =>
      ¬ GoodOrderedQuestion
        ((Finite3LinSource.ofActual I).taggedCopy K).support u) :=
  fun _ => Classical.propDecidable _

theorem actual_conflict_degree_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (q : I.RowId) :
    ((Finset.univ : Finset I.RowId).filter
      (rowConflict (Finite3LinSource.ofActual I).support q)).card ≤ 157 := by
  have hsupp : (Finite3LinSource.ofActual I).support = I.support := by
    funext r
    exact Finite3LinSource.ofActual_support I r
  have h := conflict_degree_le I.support 4 I.support_card
    (fun x => by
      have hx := rowId_incidence_card_le_four I x
      convert hx using 1
      letI : DecidablePred (fun q : I.RowId => x ∈ I.support q) :=
        fun q => Finset.decidableMem x (I.support q)
      have hfilter :
          @Finset.filter I.RowId (fun q : I.RowId => x ∈ I.support q)
              (fun q => Classical.propDecidable _)
              (Finset.univ : Finset I.RowId) =
            (Finset.univ : Finset I.RowId).filter
              (fun q => x ∈ I.support q) :=
        Finset.filter_congr_decidable _ _ _
      simpa only [hfilter] using hx)
    q
  convert h using 1
  · congr 1
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change rowConflict (Finite3LinSource.ofActual I).support q r ↔
      rowConflict I.support q r
    exact eq_iff_iff.mp (congrArg (fun s => rowConflict s q r)
      hsupp)
  · norm_num

theorem actual_tagged_row_card
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (K : Nat) :
    Fintype.card (Fin K × I.RowId) = K * I.rows.length := by
  rw [Fintype.card_prod, Fintype.card_fin,
    ActualOccurrenceAllocation.Instance.rowId_card_eq_rows_length]

theorem actual_tagged_bad_ordered_question_count_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (K J : Nat) :
    ((Finset.univ : Finset (Fin J → Fin K × I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion
        ((Finite3LinSource.ofActual I).taggedCopy K).support u)).card ≤
      J * (J - 1) * 157 * (K * I.rows.length) ^ (J - 1) := by
  have h := tagged_bad_ordered_question_count_le
    (Finite3LinSource.ofActual I) K J 157
    (actual_conflict_degree_le I)
  have hrow :=
    ActualOccurrenceAllocation.Instance.rowId_card_eq_rows_length I
  -- The generic theorem and this target elaborate their proposition filters
  -- with different proof-instance identities; identify the two filters.
  convert h using 1
  · congr 1
    apply Finset.ext
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · simp [hrow]

def actualPaddingCopies (J T : Nat) : Nat :=
  1 + T * (J * (J - 1) * 157)

theorem actualPaddingCopies_pos (J T : Nat) :
    0 < actualPaddingCopies J T := by
  simp [actualPaddingCopies]

end
end PvNP.RealizableHardness.ActualQuestionMassBridge
