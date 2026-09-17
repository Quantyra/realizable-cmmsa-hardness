import PvNP.RealizableHardness.ActualTaggedConditioningTransport

namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open ActualOccurrenceAllocation
open Finite3LinSource
open scoped BigOperators
set_option autoImplicit false
noncomputable section

theorem actualTaggedUniformMean_baseProjection_eq
    {N rowCount K J : Nat}
    (I : ActualOccurrenceAllocation.Instance N rowCount)
    (hK : 0 < K)
    (g : (Fin J → I.RowId) → ℝ) :
    actualTaggedUniformMean I K J (fun u => g (baseProjection u)) =
      (∑ q : Fin J → I.RowId, g q) /
        (Fintype.card (Fin J → I.RowId) : ℝ) := by
  let A := Fin J → Fin K
  let B := Fin J → I.RowId
  let U := Fin J → Fin K × I.RowId
  have htag : 0 < Fintype.card A := by
    apply Fintype.card_pos_iff.mpr
    let a : A := fun _ => ⟨0, hK⟩
    exact ⟨a⟩
  have htagR : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast htag
  have hsum :
      (∑ u : U, g (baseProjection u)) =
        (Fintype.card A : ℝ) * (∑ q : B, g q) := by
    have heq := Fintype.sum_equiv (taggedTupleEquiv (J := J) (K := K)
        (Row := I.RowId))
      (fun u : U => g (baseProjection u))
      (fun p : A × B => g p.2)
      (fun u => by simp [taggedTupleEquiv_apply, baseProjection])
    rw [heq]
    rw [Fintype.sum_prod_type]
    simp [A, B]
  unfold actualTaggedUniformMean
  change (∑ u : U, g (baseProjection u)) /
      (Fintype.card U : ℝ) =
    (∑ q : B, g q) / (Fintype.card B : ℝ)
  rw [hsum, taggedTuple_card, Nat.cast_mul]
  field_simp [ne_of_gt htagR] <;> ring

theorem actualTaggedGoodMean_baseProjection_le_four_thirds
    {N rowCount J T : Nat}
    (I : ActualOccurrenceAllocation.Instance N rowCount)
    (hT : 4 ≤ T) (hrows : 0 < rowCount)
    (g : (Fin J → I.RowId) → ℝ) (hg : ∀ q, 0 ≤ g q) :
    actualTaggedGoodMean I (actualPaddingCopies J T) J
      (fun u => g (baseProjection u)) ≤
      (4 : ℝ) / 3 *
        ((∑ q : Fin J → I.RowId, g q) /
          (Fintype.card (Fin J → I.RowId) : ℝ)) := by
  have h := actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg
    I J T hT hrows (fun u => g (baseProjection u))
      (fun u => hg (baseProjection u))
  rw [actualTaggedUniformMean_baseProjection_eq I
    (actualPaddingCopies_pos J T) g] at h
  exact h

end
end PvNP.RealizableHardness.ActualQuestionMassBridge
