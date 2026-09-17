import PvNP.RealizableHardness.ActualOccurrenceSoundness
import PvNP.RealizableHardness.ActualOccurrenceDegree

/-! Source draft, uncompiled: conditional regularization of the same actual
occurrence instance. No encoded constructor FP or upstream hardness theorem. -/
namespace PvNP.RealizableHardness.ActualRegularization
open ActualOccurrenceAllocation ActualOccurrenceAllocation.Instance
open scoped BigOperators
set_option autoImplicit false
noncomputable section

def rowBlowup : Nat := 1 + 18 * FixedPortCycleFamily.degree
def variableBlowup : Nat := 26 * FixedPortCycleFamily.degree
def gap (delta : Real) : Real := soundnessCoefficient * delta / (rowBlowup : Real)

theorem rowBlowup_pos : 0 < rowBlowup := by unfold rowBlowup; omega
theorem variableBlowup_pos : 0 < variableBlowup := by
  unfold variableBlowup
  exact Nat.mul_pos (by decide) FixedPortCycleFamily.degree_pos
theorem gap_pos {delta : Real} (hdelta : 0 < delta) : 0 < gap delta := by
  unfold gap
  exact div_pos (mul_pos soundnessCoefficient_pos hdelta) (by exact_mod_cast rowBlowup_pos)

variable {N m : Nat} (I : Instance N m)

theorem row_injective (q : I.RowId) : Function.Injective (I.row q) := by
  cases q with
  | inl r => exact I.originalRow_injective r
  | inr q => exact (I.tag q.1).injective.comp (ActualEqualityCloud.row_injective q.2)

theorem cloud_variable_card (n : Nat) :
    Fintype.card (ActualEqualityCloud.GlobalVar n) =
      n * FixedPortCycleFamily.degree + 5 * Fintype.card (ActualGraphEdges.Edge n) := by
  simp only [ActualEqualityCloud.GlobalVar, ActualGraphEdges.Vertex,
    PortCycleReplacement.Port, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have hd := FixedPortCycleFamily.degree_eq
  nlinarith

theorem global_variable_card : Fintype.card I.GlobalVar =
    3 * FixedPortCycleFamily.degree * m + 5 * I.edgeCount := by
  change Fintype.card (Σ v : Fin N, ActualEqualityCloud.GlobalVar (I.size v)) = _
  rw [Fintype.card_sigma]
  simp_rw [cloud_variable_card]
  rw [Finset.sum_add_distrib]
  have hp : (∑ v : Fin N, I.size v * FixedPortCycleFamily.degree) =
      3 * FixedPortCycleFamily.degree * m := by
    rw [← Finset.sum_mul, I.sum_sizes]
    ring
  rw [hp, ← Finset.mul_sum]
  rfl

theorem global_variable_card_twice_le :
    2 * Fintype.card I.GlobalVar ≤ 51 * FixedPortCycleFamily.degree * m := by
  rw [global_variable_card]
  have he := I.edge_count_bound
  nlinarith

theorem global_variable_card_le : Fintype.card I.GlobalVar ≤ variableBlowup * m := by
  have h := global_variable_card_twice_le I
  unfold variableBlowup
  nlinarith

theorem sourceExtension_yes_fraction (eta : Real) (heta : 0 ≤ eta) (hm : 0 < m)
    (y : Fin N → ZMod 2) (hy : (I.sourceViolations y : Real) ≤ eta * (m : Real)) :
    (I.violations (I.sourceExtension y) : Real) / (I.rows.length : Real) ≤ eta := by
  have ht : (0 : Real) < I.rows.length := by exact_mod_cast I.rows_length_pos hm
  have hmT : (m : Real) ≤ I.rows.length := by exact_mod_cast I.rows_length_ge
  apply (div_le_iff₀ ht).mpr
  rw [I.sourceExtension_violations]
  exact hy.trans (mul_le_mul_of_nonneg_left hmT heta)

theorem no_fraction (delta : Real) (hdelta : 0 ≤ delta) (hm : 0 < m)
    (hno : ∀ y : Fin N → ZMod 2, delta * (m : Real) ≤ (I.sourceViolations y : Real))
    (x : I.GlobalVar → ZMod 2) :
    gap delta ≤ (I.violations x : Real) / (I.rows.length : Real) := by
  have h := I.conditional_no_fraction delta hdelta hm hno x
  simpa [gap, rowBlowup] using h

/-- Properties of one existing output, not a caller-supplied output contract.
The YES and NO clauses are implications under explicit source promises. -/
structure Certificate where
  row_distinct : ∀ q : I.RowId, Function.Injective (I.row q)
  support_three : ∀ q : I.RowId, (I.support q).card = 3
  pair_intersection : ∀ a b : I.RowId, a ≠ b → (I.support a ∩ I.support b).card ≤ 1
  ordered_rows : I.rows = I.rowIndices.map (fun q => (I.row q, I.rowRhs q))
  rows_nodup : I.rows.Nodup
  degree_four : ∀ x : I.GlobalVar, ActualOccurrenceDegree.degree I x ≤ 4
  degree_ten : ∀ x : I.GlobalVar, ActualOccurrenceDegree.degree I x ≤ 10
  rows_exact : I.rows.length = m + 4 * I.edgeCount
  rows_lower : m ≤ I.rows.length
  rows_upper : I.rows.length ≤ rowBlowup * m
  variables_exact : Fintype.card I.GlobalVar = 3 * FixedPortCycleFamily.degree * m + 5 * I.edgeCount
  variables_upper : Fintype.card I.GlobalVar ≤ variableBlowup * m
  extension_exact : ∀ y : Fin N → ZMod 2, I.violations (I.sourceExtension y) = I.sourceViolations y
  yes_fraction : ∀ (eta : Real), 0 ≤ eta → 0 < m → ∀ y : Fin N → ZMod 2,
    (I.sourceViolations y : Real) ≤ eta * (m : Real) →
      (I.violations (I.sourceExtension y) : Real) / (I.rows.length : Real) ≤ eta
  no_fraction : ∀ (delta : Real), 0 ≤ delta → 0 < m →
    (∀ y : Fin N → ZMod 2, delta * (m : Real) ≤ (I.sourceViolations y : Real)) →
      ∀ x : I.GlobalVar → ZMod 2, gap delta ≤ (I.violations x : Real) / (I.rows.length : Real)

/-- Construct every field from the actual occurrence construction. -/
def certificate : Certificate I where
  row_distinct := row_injective I
  support_three := I.support_card
  pair_intersection := I.pair_intersection
  ordered_rows := I.rows_eq_map
  rows_nodup := I.rows_nodup
  degree_four := ActualOccurrenceDegree.degree_le_four I
  degree_ten := ActualOccurrenceDegree.degree_le_ten I
  rows_exact := I.rows_length
  rows_lower := I.rows_length_ge
  rows_upper := I.rows_length_le
  variables_exact := global_variable_card I
  variables_upper := global_variable_card_le I
  extension_exact := I.sourceExtension_violations
  yes_fraction := sourceExtension_yes_fraction I
  no_fraction := no_fraction I

theorem regularization : Nonempty (Certificate I) := ⟨certificate I⟩

end
end PvNP.RealizableHardness.ActualRegularization
