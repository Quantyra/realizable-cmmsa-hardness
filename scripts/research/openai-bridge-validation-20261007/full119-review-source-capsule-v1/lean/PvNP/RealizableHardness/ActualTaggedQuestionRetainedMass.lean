import PvNP.RealizableHardness.ActualTaggedQuestionMass
import Mathlib.Data.Finset.Card

namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open ActualOccurrenceAllocation
open Finite3LinSource
open scoped BigOperators
set_option autoImplicit false
noncomputable section

local instance retainedActualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance retainedActualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

local instance retainedActualConflictDecidablePred {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (q : I.RowId) :
    DecidablePred (rowConflict (Finite3LinSource.ofActual I).support q) :=
  fun _ => Classical.propDecidable _

local instance retainedActualTaggedGoodDecidablePred {N m K J : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    DecidablePred (fun u : Fin J → Fin K × I.RowId =>
      GoodOrderedQuestion ((Finite3LinSource.ofActual I).taggedCopy K).support u) :=
  fun _ => Classical.propDecidable _

local instance retainedActualTaggedBadDecidablePred {N m K J : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    DecidablePred (fun u : Fin J → Fin K × I.RowId =>
      ¬ GoodOrderedQuestion
        ((Finite3LinSource.ofActual I).taggedCopy K).support u) :=
  fun _ => Classical.propDecidable _

def actualTaggedGoodQuestions {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat) :
    Finset (Fin J → Fin K × I.RowId) :=
  (Finset.univ : Finset (Fin J → Fin K × I.RowId)).filter
    (GoodOrderedQuestion ((Finite3LinSource.ofActual I).taggedCopy K).support)

def actualTaggedBadQuestions {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat) :
    Finset (Fin J → Fin K × I.RowId) :=
  (Finset.univ : Finset (Fin J → Fin K × I.RowId)).filter
    (fun u => ¬ GoodOrderedQuestion
      ((Finite3LinSource.ofActual I).taggedCopy K).support u)

def actualTaggedGoodMass {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat) : ℚ :=
  ((actualTaggedGoodQuestions I K J).card : ℚ) /
    (Fintype.card (Fin J → Fin K × I.RowId) : ℚ)

def actualTaggedBadMass {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat) : ℚ :=
  ((actualTaggedBadQuestions I K J).card : ℚ) /
    (Fintype.card (Fin J → Fin K × I.RowId) : ℚ)

theorem actual_tagged_bad_ordered_question_uniform_mass_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat)
    (hK : 0 < K) (hm : 0 < m) :
    actualTaggedBadMass I K J ≤
      (((J * (J - 1) * 157 : Nat) : ℚ) /
        ((K * I.rows.length : Nat) : ℚ)) := by
  have hrows : 0 < I.rows.length := I.rows_length_pos hm
  have hmul := tagged_bad_ordered_question_count_mul_rowCard_le
    (Finite3LinSource.ofActual I) K J 157 (actual_conflict_degree_le I)
  have hmul' :
      (actualTaggedBadQuestions I K J).card * (K * I.rows.length) ≤
        (J * (J - 1) * 157) *
          Fintype.card (Fin J → Fin K × I.RowId) := by
    have hevent : actualTaggedBadQuestions I K J =
        (Finset.univ : Finset (Fin J → Fin K × I.RowId)).filter
          (fun u => ¬ GoodOrderedQuestion
            ((Finite3LinSource.ofActual I).taggedCopy K).support u) := by
      apply Finset.ext
      intro u
      simp [actualTaggedBadQuestions]
    rw [hevent]
    rw [← ActualOccurrenceAllocation.Instance.rowId_card_eq_rows_length I]
    convert hmul using 1
    congr 1
    apply Finset.card_bij (fun a _ => a)
    · intro a ha
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
    · intro a₁ ha₁ a₂ ha₂ h
      exact h
    · intro b hb
      refine ⟨b, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hrow : 0 < Fintype.card I.RowId := by
    rw [ActualOccurrenceAllocation.Instance.rowId_card_eq_rows_length]
    exact I.rows_length_pos hm
  have htotal : 0 < Fintype.card (Fin J → Fin K × I.RowId) := by
    have hprod : 0 < K * Fintype.card I.RowId := Nat.mul_pos hK hrow
    have hcard : Fintype.card (Fin J → Fin K × I.RowId) =
        (K * Fintype.card I.RowId) ^ J := by
      simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    rw [hcard]
    exact pow_pos hprod J
  have hden : 0 < K * I.rows.length := Nat.mul_pos hK hrows
  have htotalQ : (0 : ℚ) < Fintype.card (Fin J → Fin K × I.RowId) := by
    exact_mod_cast htotal
  have hdenQ : (0 : ℚ) < (K * I.rows.length : Nat) := by
    exact_mod_cast hden
  change ((actualTaggedBadQuestions I K J).card : ℚ) /
      (Fintype.card (Fin J → Fin K × I.RowId) : ℚ) ≤
    ((J * (J - 1) * 157 : Nat) : ℚ) /
      ((K * I.rows.length : Nat) : ℚ)
  apply (div_le_div_iff₀ htotalQ hdenQ).2
  exact_mod_cast hmul'

theorem actual_tagged_total_question_count_pos
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat)
    (hK : 0 < K) (hm : 0 < m) :
    0 < Fintype.card (Fin J → Fin K × I.RowId) := by
  have hrow : 0 < Fintype.card I.RowId := by
    rw [ActualOccurrenceAllocation.Instance.rowId_card_eq_rows_length]
    exact I.rows_length_pos hm
  have hprod : 0 < K * Fintype.card I.RowId := Nat.mul_pos hK hrow
  have hcard : Fintype.card (Fin J → Fin K × I.RowId) =
      (K * Fintype.card I.RowId) ^ J := by
    simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  rw [hcard]
  exact pow_pos hprod J

theorem actual_tagged_bad_mass_padding_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 0 < T) (hm : 0 < m) :
    actualTaggedBadMass I (actualPaddingCopies J T) J ≤ (1 : ℚ) / T := by
  have hK : 0 < actualPaddingCopies J T := actualPaddingCopies_pos J T
  have hbase := actual_tagged_bad_ordered_question_uniform_mass_le I
    (actualPaddingCopies J T) J hK hm
  have hrows : 0 < I.rows.length := I.rows_length_pos hm
  have hrows1 : 1 ≤ I.rows.length := Nat.succ_le_iff.mp hrows
  let A : Nat := J * (J - 1) * 157
  have hAT : A * T ≤ actualPaddingCopies J T * I.rows.length := by
    have h1 : T * A ≤ (T * A) * I.rows.length := by
      calc
        T * A = (T * A) * 1 := by simp
        _ ≤ (T * A) * I.rows.length := Nat.mul_le_mul_left _ hrows1
    have h2 : (T * A) * I.rows.length ≤
        (1 + T * A) * I.rows.length := by
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    rw [actualPaddingCopies]
    calc
      A * T = T * A := Nat.mul_comm _ _
      _ ≤ (1 + T * A) * I.rows.length := h1.trans h2
  have hdenNat : 0 < actualPaddingCopies J T * I.rows.length :=
    Nat.mul_pos hK hrows
  have hdenQ : (0 : ℚ) < (actualPaddingCopies J T * I.rows.length : Nat) := by
    exact_mod_cast hdenNat
  have hTQ : (0 : ℚ) < T := by exact_mod_cast hT
  have hfrac : (A : ℚ) /
      (actualPaddingCopies J T * I.rows.length : Nat) ≤ (1 : ℚ) / T := by
    apply (div_le_div_iff₀ hdenQ hTQ).2
    norm_num
    exact_mod_cast hAT
  exact hbase.trans (by simpa [A] using hfrac)

theorem actual_tagged_bad_mass_le_quarter
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m) :
    actualTaggedBadMass I (actualPaddingCopies J T) J ≤ (1 : ℚ) / 4 := by
  have hTpos : 0 < T := lt_of_lt_of_le (by decide) hT
  have hmass := actual_tagged_bad_mass_padding_le I J T hTpos hm
  have hTQ : (0 : ℚ) < T := by exact_mod_cast hTpos
  have hfourQ : (4 : ℚ) ≤ T := by exact_mod_cast hT
  have hfrac : (1 : ℚ) / T ≤ (1 : ℚ) / 4 := by
    apply (div_le_div_iff₀ hTQ (by norm_num)).2
    norm_num
    exact hT
  exact hmass.trans hfrac

theorem actual_tagged_good_bad_card_add_eq_total
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat) :
    (actualTaggedGoodQuestions I K J).card +
      (actualTaggedBadQuestions I K J).card =
      Fintype.card (Fin J → Fin K × I.RowId) := by
  let s : Finset (Fin J → Fin K × I.RowId) :=
    (Finset.univ : Finset (Fin J → Fin K × I.RowId)).filter
      (GoodOrderedQuestion ((Finite3LinSource.ofActual I).taggedCopy K).support)
  have hbad : actualTaggedBadQuestions I K J =
      (Finset.univ : Finset (Fin J → Fin K × I.RowId)) \ s := by
    apply Finset.ext
    intro u
    rw [actualTaggedBadQuestions]
    dsimp [s]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
  have hcard := Finset.card_sdiff_add_card_eq_card
    (s := s) (t := (Finset.univ : Finset (Fin J → Fin K × I.RowId)))
    (Finset.filter_subset _ _)
  rw [show actualTaggedGoodQuestions I K J = s by rfl, hbad]
  calc
    s.card + ((Finset.univ : Finset (Fin J → Fin K × I.RowId)) \ s).card =
        ((Finset.univ : Finset (Fin J → Fin K × I.RowId)) \ s).card + s.card :=
      Nat.add_comm _ _
    _ = (Finset.univ : Finset (Fin J → Fin K × I.RowId)).card := hcard
    _ = Fintype.card (Fin J → Fin K × I.RowId) := Finset.card_univ

theorem actual_tagged_good_mass_eq_one_sub_bad_mass
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (K J : Nat)
    (hK : 0 < K) (hm : 0 < m) :
    actualTaggedGoodMass I K J = 1 - actualTaggedBadMass I K J := by
  have hcard := actual_tagged_good_bad_card_add_eq_total I K J
  have htotal := actual_tagged_total_question_count_pos I K J hK hm
  have htotalQ : (0 : ℚ) < Fintype.card (Fin J → Fin K × I.RowId) := by
    exact_mod_cast htotal
  have hrat :
      (actualTaggedGoodQuestions I K J).card +
          (actualTaggedBadQuestions I K J).card =
        Fintype.card (Fin J → Fin K × I.RowId) := hcard
  have hratQ :
      ((actualTaggedGoodQuestions I K J).card : ℚ) +
          (actualTaggedBadQuestions I K J).card =
        (Fintype.card (Fin J → Fin K × I.RowId) : ℚ) := by
    exact_mod_cast hrat
  unfold actualTaggedGoodMass actualTaggedBadMass
  apply (div_eq_iff htotalQ.ne').2
  have hcancel :
      ((actualTaggedBadQuestions I K J).card : ℚ) /
          (Fintype.card (Fin J → Fin K × I.RowId) : ℚ) *
            (Fintype.card (Fin J → Fin K × I.RowId) : ℚ) =
        (actualTaggedBadQuestions I K J).card := by
    exact div_mul_cancel₀ _ htotalQ.ne'
  rw [sub_mul, one_mul, hcancel]
  linarith

theorem actual_tagged_good_mass_ge_three_quarters
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m) :
    (3 : ℚ) / 4 ≤ actualTaggedGoodMass I (actualPaddingCopies J T) J := by
  have hbad := actual_tagged_bad_mass_le_quarter I J T hT hm
  have heq := actual_tagged_good_mass_eq_one_sub_bad_mass I
    (actualPaddingCopies J T) J (actualPaddingCopies_pos J T) hm
  linarith

theorem actual_tagged_good_card_pos
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m) :
    0 < (actualTaggedGoodQuestions I (actualPaddingCopies J T) J).card := by
  have hgood := actual_tagged_good_mass_ge_three_quarters I J T hT hm
  have hgoodQ : (0 : ℚ) < actualTaggedGoodMass I (actualPaddingCopies J T) J :=
    lt_of_lt_of_le (by norm_num) hgood
  have htotal := actual_tagged_total_question_count_pos I
    (actualPaddingCopies J T) J (actualPaddingCopies_pos J T) hm
  have htotalQ : (0 : ℚ) < Fintype.card
      (Fin J → Fin (actualPaddingCopies J T) × I.RowId) := by
    exact_mod_cast htotal
  have hnumQ : (0 : ℚ) <
      (actualTaggedGoodQuestions I (actualPaddingCopies J T) J).card := by
    unfold actualTaggedGoodMass at hgoodQ
    rcases (div_pos_iff.mp hgoodQ) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge (le_of_lt htotalQ)) hneg.2)
  exact_mod_cast hnumQ

theorem actual_tagged_conditioning_factor_le_four_thirds
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m) :
    (1 : ℚ) / actualTaggedGoodMass I (actualPaddingCopies J T) J ≤ (4 : ℚ) / 3 := by
  have hg := actual_tagged_good_mass_ge_three_quarters I J T hT hm
  have hp : (0 : ℚ) < actualTaggedGoodMass I (actualPaddingCopies J T) J :=
    lt_of_lt_of_le (by norm_num) hg
  apply (div_le_iff₀ hp).2
  nlinarith

theorem actual_tagged_conditioning_factor_lt_two
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m) :
    (1 : ℚ) / actualTaggedGoodMass I (actualPaddingCopies J T) J < 2 := by
  have hg := actual_tagged_good_mass_ge_three_quarters I J T hT hm
  have hp : (0 : ℚ) < actualTaggedGoodMass I (actualPaddingCopies J T) J :=
    lt_of_lt_of_le (by norm_num) hg
  apply (div_lt_iff₀ hp).2
  nlinarith

end
end PvNP.RealizableHardness.ActualQuestionMassBridge
