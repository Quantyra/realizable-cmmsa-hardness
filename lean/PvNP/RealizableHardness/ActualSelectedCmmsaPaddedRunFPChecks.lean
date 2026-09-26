import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFP

/-!
Interface checks for the packed checked-output composition.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFPChecks

open PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFP
open Complexity

#check checkedPackedOutputTreeTag
#check checkedPackedOutputTreeTag_mem_FP
#check checkedPackedOutputTreeTag_eq
#check checkedPackedOutputTreeTag_of_output
#check paddedRunGuardCheckedTag
#check paddedRunGuardCheckedTag_mem_FP
#check paddedRunGuardCheckedTag_empty
#check packedOriginalNumeratorCellWire
#check packedOriginalNumeratorCellWire_mem_FP
#check packedOriginalNumeratorCellWire_eq_ceilDiv
#check origNumListTag
#check origNumListTag_mem_FP
#check origNumRawStep_mem_FP
#check packedExceptionNumeratorCellWire
#check packedExceptionNumeratorCellWire_mem_FP
#check packedExceptionNumeratorCellWire_eq_ceilDiv
#check origSumTag
#check origSumTag_mem_FP
#check packedLambdaPairTag_mem_FP
#check packedScaleTag_mem_FP
#check packedCommonDenTag_mem_FP
#check packedClippedNumeratorTag_mem_FP
#check packedOutputProducerArg_mem_FP
#check packedPaddedRunOutputTag_mem_FP
#check packedPaddedRunOutputTag_eq_paddedRunOutputTag_none
#check paddedRunPolicyGuardTag
#check paddedRunPolicyGuardTag_mem_FP
#check paddedRunPolicyGuardTag_eq
#check paddedRunPolicyGuardTag_none
#check paddedRunOutputTag_of_policy_empty
#check origNumArgWeights_some
#check decodedInputParamsTag_some
#check packedLambdaPairTag_some
#check origNumArgLambda_some
#check packedNMBitsTag_some
#check packedBudgetPairTag_some
#check origNumArgScale_eq_of_components
#check packedExceptionItemOf_eq_of_components

#print axioms checkedPackedOutputTreeTag_mem_FP
#print axioms paddedRunGuardCheckedTag_mem_FP
#print axioms packedOriginalNumeratorCellWire_mem_FP
#print axioms packedOriginalNumeratorCellWire_eq_ceilDiv
#print axioms checkedPackedOutputTreeTag_of_output
#print axioms origNumListTag_mem_FP
#print axioms packedExceptionNumeratorCellWire_mem_FP
#print axioms origSumTag_mem_FP
#print axioms packedCommonDenTag_mem_FP
#print axioms packedClippedNumeratorTag_mem_FP
#print axioms packedPaddedRunOutputTag_mem_FP
#print axioms packedPaddedRunOutputTag_eq_paddedRunOutputTag_none
#print axioms paddedRunPolicyGuardTag_mem_FP
#print axioms paddedRunPolicyGuardTag_eq
#print axioms paddedRunPolicyGuardTag_none
#print axioms paddedRunOutputTag_of_policy_empty
#print axioms origNumArgWeights_some
#print axioms packedLambdaPairTag_some
#print axioms origNumArgLambda_some
#print axioms packedNMBitsTag_some
#print axioms packedBudgetPairTag_some
#print axioms origNumArgScale_eq_of_components
#print axioms packedExceptionItemOf_eq_of_components

example (L : Nat) (eps : Rat)
    (producer : List Bool → List Bool) :
    paddedRunGuardCheckedTag L eps producer [] = [] :=
  paddedRunGuardCheckedTag_empty L eps producer

end PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFPChecks
