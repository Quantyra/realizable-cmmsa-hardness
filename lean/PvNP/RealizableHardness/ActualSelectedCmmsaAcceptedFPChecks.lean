import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFP

/-!
Interface checks for the packed CMMSA acceptance transducer.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFPChecks

open PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFP
open Complexity

#check acceptedShapeFlag
#check acceptedShapeFlag_mem_FP
#check acceptedFormulasNonemptyFlag
#check acceptedFormulasNonemptyFlag_mem_FP
#check acceptedBudgetRangeFlag
#check acceptedBudgetRangeFlag_mem_FP
#check acceptedWeightSumFlag
#check acceptedWeightSumFlag_mem_FP
#check formulaLeavesOkTag
#check formulaLeavesOkTag_mem_FP
#check acceptedFormulaListFlag
#check acceptedFormulaListFlag_mem_FP
#check acceptedTag
#check acceptedTag_mem_FP
#check checkedTreeTag
#check checkedTreeTag_mem_FP
#check acceptedTag_nil
#check checkedTreeTag_nil
#check acceptedShapeFlag_leaf
#check acceptedTag_leaf

#print axioms acceptedShapeFlag_mem_FP
#print axioms acceptedFormulasNonemptyFlag_mem_FP
#print axioms acceptedBudgetRangeFlag_mem_FP
#print axioms acceptedWeightSumFlag_mem_FP
#print axioms formulaLeavesOkTag_mem_FP
#print axioms acceptedFormulaListFlag_mem_FP
#print axioms acceptedTag_mem_FP
#print axioms checkedTreeTag_mem_FP
#print axioms acceptedTag_nil
#print axioms checkedTreeTag_nil
#print axioms acceptedShapeFlag_leaf
#print axioms acceptedTag_leaf

example (L : Nat) : acceptedTag L [] = [] := acceptedTag_nil L
example (L : Nat) : checkedTreeTag L [] = [] := checkedTreeTag_nil L
example (L : Nat) :
    acceptedTag L (CMMSACodec.Tree.encode .leaf) = [] :=
  acceptedTag_leaf L

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFPChecks
