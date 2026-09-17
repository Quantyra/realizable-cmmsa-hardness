import PvNP.RealizableHardness.ActualTreeParseFP

/-!
Interface checks for the packed Tree.parse FP tag. This file does not inhabit
`hSrcCmmsa` and does not assert unconditional Theorem 1, Corollary 2, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualTreeParseFPChecks
open Complexity
open PvNP.RealizableHardness.ActualTreeParseFP
open PvNP.RealizableHardness.CMMSACodec

#check treeParseTag
#check treeParseTag_empty
#check treeParseTag_none
#check treeParseTag_some
#check treeParseTag_leaf
#check treeParseTag_mem_FP

#print axioms treeParseTag_empty
#print axioms treeParseTag_none
#print axioms treeParseTag_some
#print axioms treeParseTag_leaf
#print axioms treeParseTag_mem_FP

example : treeParseTag [] = [] := treeParseTag_empty

example : treeParseTag [false] = true :: Complexity.pair [false] [] := treeParseTag_leaf

example : treeParseTag [true] = [] := rfl

example : treeParseTag ∈ Complexity.FP := treeParseTag_mem_FP

end PvNP.RealizableHardness.ActualTreeParseFPChecks
