import PvNP.RealizableHardness.ExecutableRounding

/-! UNCOMPILED checks. No kernel or executable-result evidence is yet claimed. -/
open PvNP.RealizableHardness
open ExecutableRounding

#print axioms numerators_length
#print axioms outputWeights_length
#print axioms lambda_eq
#print axioms budget_eq
#print axioms repairedAt_eq
#print axioms scale_eq
#print axioms numerators_eq
#print axioms denominator_eq
#print axioms clippedNumerator_eq
#print axioms outputWeights_eq
#print axioms outputBudget_eq
#print axioms outputData_fields
#print axioms original_repairedAt
#print axioms exception_repairedAt
#print axioms denominator_bound
#print axioms positive_integer_data
#print axioms read_fractionTree
#print axioms fractionTree_length
#print axioms read_weightTree
#print axioms read_budgetTree
#print axioms listTree_length_bound
#print axioms arithmetic_wire_bound
#print axioms inverse_le_denominator
#print axioms input_denominator_bound
#print axioms input_arithmetic_wire_bound
#print axioms read_semantic_fields

namespace PvNP.RealizableHardness.ExecutableRoundingChecks

def sample : InputParameters := ⟨1, 0, 1/4, 8⟩
def clipping : InputParameters := ⟨1, 1, 1, 1⟩

private theorem clog792 : Nat.clog 2 792 = 10 := by
  have hl : 9 < Nat.clog 2 792 := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num)
  have hu : Nat.clog 2 792 ≤ 10 := (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by norm_num)
  omega

private theorem clog24 : Nat.clog 2 24 = 5 := by
  have hl : 4 < Nat.clog 2 24 := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num)
  have hu : Nat.clog 2 24 ≤ 5 := (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by norm_num)
  omega

private theorem sampleScale : roundingScale [1] 1 sample = 1024 := by
  norm_num [roundingScale, WeightRounding.dyadicScale, repairBudget, repairLambda, sample, clog792]

private theorem clippingScale : roundingScale [1] 1 clipping = 32 := by
  norm_num [roundingScale, WeightRounding.dyadicScale, repairBudget, repairLambda, clipping, clog24]

private theorem sampleNumerators : numerators [1] 1 sample = [32, 993] := by
  have h0 : ⌈(1024 : Rat)/33⌉₊ = 32 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  have h1 : ⌈(32768 : Rat)/33⌉₊ = 993 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  unfold numerators
  rw [sampleScale]
  norm_num [List.ofFn_succ, WeightRounding.coordinate, flatRepairedAt, repairedAt,
    repairLambda, sample, h0, h1, finSumFinEquiv, Fin.addCases]

private theorem clippingNumerators : numerators [1] 1 clipping = [16, 16] := by
  unfold numerators
  rw [clippingScale]
  norm_num [List.ofFn_succ, WeightRounding.coordinate, flatRepairedAt, repairedAt,
    repairLambda, clipping, finSumFinEquiv, Fin.addCases]

example : roundingScale [1] 1 sample = 1024 := sampleScale
example : numerators [1] 1 sample = [32, 993] := sampleNumerators
example : commonDenominator [1] 1 sample = 1025 := by
  norm_num [commonDenominator, sampleNumerators]
example : outputWeights [1] 1 sample = [32/1025, 993/1025] := by
  norm_num [outputWeights, commonDenominator, sampleNumerators]
example : outputBudget [1] 1 sample = 34/1025 := by
  have hc : ⌈(1024 : Rat)/33⌉₊ = 32 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  simp only [outputBudget, clippedNumerator, commonDenominator, sampleNumerators, sampleScale]
  norm_num [repairBudget, repairLambda, sample, hc]

-- Invalid scalar data still exercises the exact clipping branch.
example : clippedNumerator [1] 1 clipping = 32 := by
  simp only [clippedNumerator, commonDenominator, clippingNumerators, clippingScale]
  norm_num [repairBudget, repairLambda, clipping]
example : outputBudget [1] 1 clipping = 1 := by
  simp only [outputBudget, clippedNumerator, commonDenominator, clippingNumerators, clippingScale]
  norm_num [repairBudget, repairLambda, clipping]

-- Empty raw lists remain total without asserting input validity.
example : outputWeights [] 0 sample = [] := by simp [outputWeights, numerators]
example : outputBudget [] 0 sample = 0 := by
  simp [outputBudget, clippedNumerator, commonDenominator, numerators]

example (ws : List Rat) (M : Nat) (q : InputParameters) (i : Fin M) :
    flatRepairedAt ws M q (finSumFinEquiv (Sum.inr i)) =
      (repairLambda q / (M : Rat)) / (1 + repairLambda q) :=
  exception_repairedAt ws M q i

#eval numerators [1] 1 sample
#eval outputBudget [1] 1 sample
#eval clippedNumerator [1] 1 clipping

end PvNP.RealizableHardness.ExecutableRoundingChecks
