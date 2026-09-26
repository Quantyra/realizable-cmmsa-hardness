import PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq

/-!
Interface checks for `acceptedTag` semantic agreement lemmas.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqChecks

open PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEq
open PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedFP
open PvNP.RealizableHardness.ExecutableRounding
open Complexity

#check acceptedShapeFlag_node_leaf
#check acceptedShapeFlag_node_node
#check acceptedFormulasNonemptyFlag_leaf_formulas
#check acceptedFormulasNonemptyFlag_node_formulas
#check acceptedBudgetBits_of_output
#check acceptedBudgetNum_of_fraction
#check acceptedBudgetDen_of_fraction
#check acceptedBudgetRangeFlag_of_fraction
#check accWRawStep_of_nil
#check accWRawStep_of_cons_pos
#check acceptedTag_eq_leaf
#check acceptedTag_eq_node_leaf
#check acceptedTag_of_output_shape
#check accWClamp_eq_of_length_le
#check accWBoundedStep_canonical_nil
#check accWBoundedStep_canonical_cons
#check checkedTreeTag_eq_checkedOutput_of_acceptedTag

#print axioms acceptedShapeFlag_node_node
#print axioms acceptedBudgetRangeFlag_of_fraction
#print axioms accWRawStep_of_cons_pos
#print axioms acceptedTag_eq_leaf
#print axioms acceptedTag_eq_node_leaf
#print axioms acceptedTag_of_output_shape
#print axioms accWBoundedStep_canonical_nil
#print axioms accWBoundedStep_canonical_cons
#print axioms checkedTreeTag_eq_checkedOutput_of_acceptedTag

example (L : Nat) :
    acceptedTag L (CMMSACodec.Tree.encode .leaf) =
      if CMMSACodec.accepted L .leaf then [true] else [] :=
  acceptedTag_eq_leaf L

end PvNP.RealizableHardness.ActualSelectedCmmsaAcceptedEqChecks
