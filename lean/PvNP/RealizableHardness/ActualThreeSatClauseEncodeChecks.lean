import PvNP.RealizableHardness.ActualThreeSatClauseEncode

/-!
Checks for the 3SAT-tape-dependent 3-OR CMMSA encoder.
Tiny examples first; axiom prints after.

Does not inhabit `hSrcCmmsa`.  There is no `Yes 0` / `decode` /
`MapReducesVia` theorem here.  The source row is a constant 3-OR, so
this is not a No-map for unsat 3SAT.  LeafFold/`unsatCnf` is not used.
-/
namespace PvNP.RealizableHardness.ActualThreeSatClauseEncodeChecks

open PvNP.RealizableHardness.ActualThreeSatClauseEncode
open PvNP.RealizableHardness.ActualThreeSatToEncodeInput
open PvNP.RealizableHardness.ActualThreeSatCmmsaReduce

#check clause3
#check clause3_leaves
#check threeSatToClauseEncodeInput
#check threeSatToClauseEncodeInput_mem_FP
#check threeSatToClauseEncodeInput_ne_id
#check threeSatToClauseEncodeInput_ne_tautology
#check treeEncode_inj
#check compiledClauseTree_ne_compiledTree
#check threeSatClauseMap
#check threeSatClauseMap_apply
#check compiledClauseInput

example : Formula.leaves clause3 = 3 := clause3_leaves

example : threeSatToClauseEncodeInput [] ≠ [] :=
  threeSatToClauseEncodeInput_ne_id

example : threeSatToClauseEncodeInput [] ≠ threeSatToEncodeInput [] :=
  threeSatToClauseEncodeInput_ne_tautology

#print axioms clause3_leaves
#print axioms threeSatToClauseEncodeInput_mem_FP
#print axioms threeSatToClauseEncodeInput_ne_id
#print axioms treeEncode_inj
#print axioms compiledClauseTree_ne_compiledTree
#print axioms threeSatToClauseEncodeInput_ne_tautology

end PvNP.RealizableHardness.ActualThreeSatClauseEncodeChecks
