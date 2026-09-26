import PvNP.RealizableHardness.ActualThreeSatClauseOrFp

/-!
Checks for thin `clauseOrEnc ∈ Complexity.FP`.

Does not inhabit `hSrcCmmsa`.  Not a packed Yes/No `encodeData` map.
-/
namespace PvNP.RealizableHardness.ActualThreeSatClauseOrFpChecks

open PvNP.RealizableHardness.ActualThreeSatClauseOrFp
open Complexity

#check encodeDigitsFn_mem_FP
#check unaryBitsFn_mem_FP
#check varTreeEnc_mem_FP
#check clauseVarTreeFn_mem_FP
#check clauseOrEnc
#check clauseOrEnc_mem_FP
#check clauseOrEnc_ne_id

example : clauseOrEnc ∈ Complexity.FP := clauseOrEnc_mem_FP

example : clauseOrEnc [] ≠ [] := clauseOrEnc_ne_id

example : varTreeEnc ∈ Complexity.FP := varTreeEnc_mem_FP

#print axioms encodeDigitsFn_mem_FP
#print axioms unaryBitsFn_mem_FP
#print axioms varTreeEnc_mem_FP
#print axioms clauseVarTreeFn_mem_FP
#print axioms clauseOrEnc_mem_FP
#print axioms clauseOrEnc_ne_id

end PvNP.RealizableHardness.ActualThreeSatClauseOrFpChecks
