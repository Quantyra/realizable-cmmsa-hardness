import PvNP.RealizableHardness.ActualTaggedBaseProjectionTransport
import PvNP.RealizableHardness.ActualOccurrenceCompleteness

namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open ActualOccurrenceAllocation
open Finite3LinSource
open scoped BigOperators
set_option autoImplicit false
noncomputable section
local instance failureActualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance failureActualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

def actualTaggedFailureIndicator
    {N m K J : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2)
    (u : Fin J → Fin K × I.RowId) : ℝ := by
  letI : DecidableEq (Fin K × I.RowId) := instDecidableEqProd
  letI : Decidable (∃ j : Fin J,
      ((Finite3LinSource.ofActual I).taggedCopy K).badRow
        (Finite3LinSource.repeatAssignment (K := K) x) (u j) = true) :=
    Classical.propDecidable _
  exact if ∃ j : Fin J,
      ((Finite3LinSource.ofActual I).taggedCopy K).badRow
        (Finite3LinSource.repeatAssignment (K := K) x) (u j) = true
    then 1 else 0

def actualBaseFailureIndicator
    {N m J : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2) (q : Fin J → I.RowId) : ℝ := by
  classical
  exact if ∃ j : Fin J, (Finite3LinSource.ofActual I).badRow x (q j) = true then 1 else 0

theorem actualTaggedFailureIndicator_eq_baseProjection
    {N m K J : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2) (u : Fin J → Fin K × I.RowId) :
    actualTaggedFailureIndicator I x u =
      actualBaseFailureIndicator I x (baseProjection u) := by
  letI : DecidableEq (Fin K × I.GlobalVar) := instDecidableEqProd
  unfold actualTaggedFailureIndicator actualBaseFailureIndicator
  have hiff :
      (∃ j : Fin J, ((Finite3LinSource.ofActual I).taggedCopy K).badRow
        (Finite3LinSource.repeatAssignment (K := K) x) (u j) = true) ↔
      (∃ j : Fin J, (Finite3LinSource.ofActual I).badRow x ((baseProjection u) j) = true) := by
    constructor <;> rintro ⟨j, hj⟩ <;> refine ⟨j, ?_⟩
    · rw [Finite3LinSource.taggedCopy_badRow,
        Finite3LinSource.restrictAssignment_repeatAssignment] at hj
      exact hj
    · rw [Finite3LinSource.taggedCopy_badRow,
        Finite3LinSource.restrictAssignment_repeatAssignment]
      exact hj
  by_cases hp :
      ∃ j : Fin J, ((Finite3LinSource.ofActual I).taggedCopy K).badRow
        (Finite3LinSource.repeatAssignment (K := K) x) (u j) = true
  · have hq := hiff.mp hp
    simp [hp, hq]
  · have hq := hiff.not.mp hp
    simp [hp, hq]

theorem actualBaseFailureIndicator_nonneg
    {N m J : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2) (q : Fin J → I.RowId) :
    0 ≤ actualBaseFailureIndicator I x q := by
  unfold actualBaseFailureIndicator
  split <;> norm_num

theorem actualBaseFailureIndicator_le_sum
    {N m J : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2) (q : Fin J → I.RowId) :
    actualBaseFailureIndicator I x q ≤
      ∑ j : Fin J, if (Finite3LinSource.ofActual I).badRow x (q j) then (1 : ℝ) else 0 := by
  unfold actualBaseFailureIndicator
  split
  · rename_i h
    obtain ⟨j, hj⟩ := h
    calc
      (1 : ℝ) = (if (Finite3LinSource.ofActual I).badRow x (q j) then 1 else 0) := by simp [hj]
      _ ≤ ∑ i : Fin J, if (Finite3LinSource.ofActual I).badRow x (q i) then (1 : ℝ) else 0 := by
        apply Finset.single_le_sum (fun i _ => by split <;> norm_num) (Finset.mem_univ j)
  · exact Finset.sum_nonneg (fun j _ => by split <;> norm_num)

theorem sum_eval_eq_card_pow_mul_sum
    {J : Nat} {E : Type*} [Fintype E] [DecidableEq E]
    (j : Fin J) (f : E → ℝ) :
    (∑ q : Fin J → E, f (q j)) =
      (Fintype.card E : ℝ) ^ (J - 1) * ∑ e : E, f e := by
  let K := {i : Fin J // i ≠ j}
  let encode : (Fin J → E) ≃ E × (K → E) :=
    { toFun := fun q => (q j, fun i => q i.1)
      invFun := fun p i => if h : i = j then p.1 else p.2 ⟨i, h⟩
      left_inv := by
        intro q
        funext i
        by_cases h : i = j
        · subst i; simp
        · simp [h]
      right_inv := by
        intro p
        apply Prod.ext
        · simp
        · funext i
          simp [i.2] }
  have hcard : Fintype.card K = J - 1 := by
    rw [Fintype.card_subtype]
    have hf : ({i : Fin J | i ≠ j} : Finset (Fin J)) = Finset.univ.erase j := by
      ext i
      simp [ne_comm]
    rw [hf, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin]
  rw [Fintype.sum_equiv encode (fun q => f (q j))
    (fun p : E × (K → E) => f p.1) (fun q => rfl)]
  rw [Fintype.sum_prod_type]
  simp [hcard]
  rw [← Finset.mul_sum]

theorem actualBaseFailureIndicator_uniformMean_le
    {N m J : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (hm : 0 < m) (x : I.GlobalVar → ZMod 2) :
    (∑ q : Fin J → I.RowId, actualBaseFailureIndicator I x q) /
        (Fintype.card (Fin J → I.RowId) : ℝ) ≤
      (J : ℝ) * ((Finite3LinSource.ofActual I).violations x : ℝ) /
        (Fintype.card I.RowId : ℝ) := by
  have hrowNat : 0 < Fintype.card I.RowId := by
    rw [I.rowId_card_eq_rows_length]
    exact I.rows_length_pos hm
  have hrow : (0 : ℝ) < Fintype.card I.RowId := by exact_mod_cast hrowNat
  by_cases hJ : J = 0
  · subst J
    simp [actualBaseFailureIndicator]
  · have hsum :
        (∑ q : Fin J → I.RowId, actualBaseFailureIndicator I x q) ≤
          ∑ q : Fin J → I.RowId,
            ∑ j : Fin J, if (Finite3LinSource.ofActual I).badRow x (q j)
              then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      exact actualBaseFailureIndicator_le_sum I x q
    have hsum' :
        (∑ q : Fin J → I.RowId, actualBaseFailureIndicator I x q) ≤
          ∑ j : Fin J, (Fintype.card I.RowId : ℝ) ^ (J - 1) *
            ∑ e : I.RowId, if (Finite3LinSource.ofActual I).badRow x e
              then (1 : ℝ) else 0 := by
      calc
        _ ≤ ∑ q : Fin J → I.RowId,
            ∑ j : Fin J, if (Finite3LinSource.ofActual I).badRow x (q j)
              then (1 : ℝ) else 0 := hsum
        _ = ∑ j : Fin J, ∑ q : Fin J → I.RowId,
            if (Finite3LinSource.ofActual I).badRow x (q j)
              then (1 : ℝ) else 0 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          exact sum_eval_eq_card_pow_mul_sum j
            (fun e : I.RowId => if (Finite3LinSource.ofActual I).badRow x e
              then (1 : ℝ) else 0)
    have hflags :
        (∑ e : I.RowId, if (Finite3LinSource.ofActual I).badRow x e then (1 : ℝ) else 0) =
          ((Finite3LinSource.ofActual I).violations x : ℝ) := by
      unfold Finite3LinSource.violations
      norm_cast
    rw [hflags, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum'
    simp only [Fintype.card_fin] at hsum'
    have hpow : (Fintype.card I.RowId : ℝ) ^ J =
        (Fintype.card I.RowId : ℝ) ^ (J - 1) * Fintype.card I.RowId := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hJ)]
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, hpow]
    apply (div_le_div_iff₀ (mul_pos (pow_pos hrow _) hrow) hrow).2
    calc
      (∑ q : Fin J → I.RowId, actualBaseFailureIndicator I x q) *
          (Fintype.card I.RowId : ℝ) ≤
          ((J : ℝ) * ((Fintype.card I.RowId : ℝ) ^ (J - 1) *
            ((Finite3LinSource.ofActual I).violations x : ℝ))) *
            (Fintype.card I.RowId : ℝ) :=
        mul_le_mul_of_nonneg_right hsum' (le_of_lt hrow)
      _ = ((J : ℝ) * ((Finite3LinSource.ofActual I).violations x : ℝ)) *
          ((Fintype.card I.RowId : ℝ) ^ (J - 1) * Fintype.card I.RowId) := by ring

theorem actualSourceExtension_failureRate_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta)
    (y : Fin N → ZMod 2)
    (hy : (I.sourceViolations y : ℝ) ≤ eta * (m : ℝ)) :
    ((Finite3LinSource.ofActual I).violations (I.sourceExtension y) : ℝ) /
        (Fintype.card I.RowId : ℝ) ≤ eta := by
  rw [Finite3LinSource.ofActual_violations, I.sourceExtension_violations]
  have hrowNat : 0 < Fintype.card I.RowId := by
    rw [I.rowId_card_eq_rows_length]
    exact I.rows_length_pos hm
  have hrow : (0 : ℝ) < Fintype.card I.RowId := by exact_mod_cast hrowNat
  apply (div_le_iff₀ hrow).2
  calc
    (I.sourceViolations y : ℝ) ≤ eta * (m : ℝ) := hy
    _ ≤ eta * (Fintype.card I.RowId : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ heta
      rw [I.rowId_card_eq_rows_length]
      exact_mod_cast I.rows_length_ge

theorem actualTaggedGoodFailureMean_sourceExtension_le
    {N m J T : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (hT : 4 ≤ T) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta)
    (y : Fin N → ZMod 2)
    (hy : (I.sourceViolations y : ℝ) ≤ eta * (m : ℝ)) :
    actualTaggedGoodMean I (actualPaddingCopies J T) J
      (actualTaggedFailureIndicator I (I.sourceExtension y)) ≤
      (4 : ℝ) / 3 * (J : ℝ) * eta := by
  rw [show actualTaggedFailureIndicator I (I.sourceExtension y) =
      fun u => actualBaseFailureIndicator I (I.sourceExtension y) (baseProjection u) by
    funext u
    exact actualTaggedFailureIndicator_eq_baseProjection I (I.sourceExtension y) u]
  have hc := actualTaggedGoodMean_baseProjection_le_four_thirds (J := J) I hT hm
    (actualBaseFailureIndicator I (I.sourceExtension y))
    (actualBaseFailureIndicator_nonneg (J := J) I (I.sourceExtension y))
  have hu := actualBaseFailureIndicator_uniformMean_le (J := J) I hm (I.sourceExtension y)
  have hr := actualSourceExtension_failureRate_le I hm eta heta y hy
  have hJnonneg : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hfactor : (0 : ℝ) ≤ 4 / 3 := by norm_num
  calc
    _ ≤ (4 : ℝ) / 3 *
        ((∑ q : Fin J → I.RowId, actualBaseFailureIndicator I (I.sourceExtension y) q) /
          (Fintype.card (Fin J → I.RowId) : ℝ)) := hc
    _ ≤ (4 : ℝ) / 3 * ((J : ℝ) *
        ((Finite3LinSource.ofActual I).violations (I.sourceExtension y) : ℝ) /
          (Fintype.card I.RowId : ℝ)) := by
      gcongr
    _ = (4 : ℝ) / 3 * ((J : ℝ) *
        (((Finite3LinSource.ofActual I).violations (I.sourceExtension y) : ℝ) /
          (Fintype.card I.RowId : ℝ))) := by ring
    _ ≤ (4 : ℝ) / 3 * ((J : ℝ) * eta) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hJnonneg) hfactor
    _ = (4 : ℝ) / 3 * (J : ℝ) * eta := by ring

end
end PvNP.RealizableHardness.ActualQuestionMassBridge
