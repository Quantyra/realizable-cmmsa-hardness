import PvNP.RealizableHardness.ActualTaggedFailureTransport

namespace PvNP.RealizableHardness.ActualTaggedFailureTransportChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualQuestionMassBridge
open scoped BigOperators
noncomputable section

local instance checksActualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance checksActualGlobalVarDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

#check actualTaggedFailureIndicator
#check actualBaseFailureIndicator
#check actualTaggedFailureIndicator_eq_baseProjection
#check actualBaseFailureIndicator_nonneg
#check actualBaseFailureIndicator_le_sum
#check sum_eval_eq_card_pow_mul_sum
#check actualBaseFailureIndicator_uniformMean_le
#check actualSourceExtension_failureRate_le
#check actualTaggedGoodFailureMean_sourceExtension_le

#print axioms actualTaggedFailureIndicator_eq_baseProjection
#print axioms actualBaseFailureIndicator_nonneg
#print axioms actualBaseFailureIndicator_le_sum
#print axioms sum_eval_eq_card_pow_mul_sum
#print axioms actualBaseFailureIndicator_uniformMean_le
#print axioms actualSourceExtension_failureRate_le
#print axioms actualTaggedGoodFailureMean_sourceExtension_le

def oneRowActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 0

def oneRowAssignment : oneRowActual.GlobalVar → ZMod 2 := fun _ => 0

example : actualBaseFailureIndicator oneRowActual oneRowAssignment
    (fun _ : Fin 0 => Sum.inl 0) = 0 := by
  simp [actualBaseFailureIndicator]

example : actualBaseFailureIndicator oneRowActual oneRowAssignment
    (fun _ : Fin 1 => Sum.inl 0) = 0 := by
  simp [actualBaseFailureIndicator, oneRowActual, oneRowAssignment,
    Finite3LinSource.ofActual, Finite3LinSource.badRow,
    ActualOccurrenceAllocation.Instance.rowRhs]

def twoRowActual : ActualOccurrenceAllocation.Instance 1 2 where
  vars := fun _ _ => 0
  rhs := fun _ => 1

def twoRowAssignment : twoRowActual.GlobalVar → ZMod 2 := fun _ => 0

example : actualBaseFailureIndicator twoRowActual twoRowAssignment
    (fun j : Fin 1 => if j = 0 then Sum.inl 0 else Sum.inl 1) = 1 := by
  norm_num [actualBaseFailureIndicator, twoRowActual, twoRowAssignment,
    Finite3LinSource.ofActual, Finite3LinSource.badRow,
    ActualOccurrenceAllocation.Instance.rowRhs]

example : actualBaseFailureIndicator twoRowActual twoRowAssignment
    (fun _ : Fin 0 => Sum.inl 0) = 0 := by
  simp [actualBaseFailureIndicator]

example :
    actualTaggedGoodMean oneRowActual (actualPaddingCopies 0 4) 0
      (actualTaggedFailureIndicator oneRowActual
        (oneRowActual.sourceExtension (fun _ => 0))) ≤
      (4 : ℝ) / 3 * (0 : ℝ) * 0 := by
  have h := actualTaggedGoodFailureMean_sourceExtension_le (J := 0) (T := 4)
    oneRowActual (by norm_num) (by norm_num) 0 (by norm_num) (fun _ => 0)
    (by simp [ActualOccurrenceAllocation.Instance.sourceViolations,
      ActualOccurrenceAllocation.Instance.sourceBadRow, oneRowActual])
  simpa using h

example :
    (∑ q : Fin 1 → twoRowActual.RowId,
        actualBaseFailureIndicator twoRowActual twoRowAssignment q) /
        (Fintype.card (Fin 1 → twoRowActual.RowId) : ℝ) ≤
      (1 : ℝ) * ((Finite3LinSource.ofActual twoRowActual).violations twoRowAssignment : ℝ) /
        (Fintype.card twoRowActual.RowId : ℝ) := by
  convert actualBaseFailureIndicator_uniformMean_le (J := 1) twoRowActual
    (by norm_num) twoRowAssignment using 1 <;> norm_num

example (eta : ℝ) (heta : 0 ≤ eta)
    (hy : (twoRowActual.sourceViolations (fun _ => 0) : ℝ) ≤ eta * (2 : ℝ)) :
    ((Finite3LinSource.ofActual twoRowActual).violations
      (twoRowActual.sourceExtension (fun _ => 0)) : ℝ) /
        (Fintype.card twoRowActual.RowId : ℝ) ≤ eta := by
  apply actualSourceExtension_failureRate_le twoRowActual (by norm_num) eta heta
  exact hy

end
end PvNP.RealizableHardness.ActualTaggedFailureTransportChecks
